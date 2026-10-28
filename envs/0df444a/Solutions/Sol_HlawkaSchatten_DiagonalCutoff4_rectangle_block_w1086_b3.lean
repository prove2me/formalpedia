-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:55:00.497156+00:00
-- url     : https://prove2.me/submissions/02f67b83-ef08-41aa-b330-5e0c34b71a6c

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
theorem support_rectangle_w1086_box_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-129073909/625000000 : ℝ)*x 0 + (5377095349/10000000000 : ℝ)*x 1 + (13442739/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129073909/625000000 : ℝ)^8279 ≤ (3002199843/24414062500 : ℝ)^6231 := by
    have hnat : (129073909 : ℕ)^8279*24414062500^6231 ≤ 3002199843^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129073909 625000000 3002199843 24414062500 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377095349/10000000000 : ℝ)^8279 ≤ (43851493350463/100000000000000 : ℝ)^6231 := by
    have hnat : (5377095349 : ℕ)^8279*100000000000000^6231 ≤ 43851493350463^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377095349 10000000000 43851493350463 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13442739/25000000 : ℝ)^8279 ≤ (43851496070223/100000000000000 : ℝ)^6231 := by
    have hnat : (13442739 : ℕ)^8279*100000000000000^6231 ≤ 43851496070223^6231*25000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13442739 25000000 43851496070223 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129073909/625000000 : ℝ), (5377095349/10000000000 : ℝ), (13442739/25000000 : ℝ)] ![(3002199843/24414062500 : ℝ), (43851493350463/100000000000000 : ℝ), (43851496070223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129073909/625000000 : ℝ)|^8279 ≤ (3002199843/24414062500 : ℝ)^6231
        have hw : |(-129073909/625000000 : ℝ)|=(129073909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377095349/10000000000 : ℝ)|^8279 ≤ (43851493350463/100000000000000 : ℝ)^6231
        have hw : |(5377095349/10000000000 : ℝ)|=(5377095349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13442739/25000000 : ℝ)|^8279 ≤ (43851496070223/100000000000000 : ℝ)^6231
        have hw : |(13442739/25000000 : ℝ)|=(13442739/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647711079/5000000000 : ℝ)*x 0 + (-1087900039/5000000000 : ℝ)*x 1 + (5377095643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647711079/5000000000 : ℝ)^8279 ≤ (5371090521857/12500000000000 : ℝ)^6231 := by
    have hnat : (2647711079 : ℕ)^8279*12500000000000^6231 ≤ 5371090521857^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647711079 5000000000 5371090521857 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087900039/5000000000 : ℝ)^8279 ≤ (263595585441/2000000000000 : ℝ)^6231 := by
    have hnat : (1087900039 : ℕ)^8279*2000000000000^6231 ≤ 263595585441^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087900039 5000000000 263595585441 2000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377095643/10000000000 : ℝ)^8279 ≤ (21925748268079/50000000000000 : ℝ)^6231 := by
    have hnat : (5377095643 : ℕ)^8279*50000000000000^6231 ≤ 21925748268079^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377095643 10000000000 21925748268079 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647711079/5000000000 : ℝ), (-1087900039/5000000000 : ℝ), (5377095643/10000000000 : ℝ)] ![(5371090521857/12500000000000 : ℝ), (263595585441/2000000000000 : ℝ), (21925748268079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647711079/5000000000 : ℝ)|^8279 ≤ (5371090521857/12500000000000 : ℝ)^6231
        have hw : |(2647711079/5000000000 : ℝ)|=(2647711079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087900039/5000000000 : ℝ)|^8279 ≤ (263595585441/2000000000000 : ℝ)^6231
        have hw : |(-1087900039/5000000000 : ℝ)|=(1087900039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377095643/10000000000 : ℝ)|^8279 ≤ (21925748268079/50000000000000 : ℝ)^6231
        have hw : |(5377095643/10000000000 : ℝ)|=(5377095643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295422647/10000000000 : ℝ)*x 0 + (5377095207/10000000000 : ℝ)*x 1 + (-2175800011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295422647/10000000000 : ℝ)^8279 ≤ (21484364723461/50000000000000 : ℝ)^6231 := by
    have hnat : (5295422647 : ℕ)^8279*50000000000000^6231 ≤ 21484364723461^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295422647 10000000000 21484364723461 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377095207/10000000000 : ℝ)^8279 ≤ (8770298362359/20000000000000 : ℝ)^6231 := by
    have hnat : (5377095207 : ℕ)^8279*20000000000000^6231 ≤ 8770298362359^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377095207 10000000000 8770298362359 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175800011/10000000000 : ℝ)^8279 ≤ (1647472341601/12500000000000 : ℝ)^6231 := by
    have hnat : (2175800011 : ℕ)^8279*12500000000000^6231 ≤ 1647472341601^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175800011 10000000000 1647472341601 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295422647/10000000000 : ℝ), (5377095207/10000000000 : ℝ), (-2175800011/10000000000 : ℝ)] ![(21484364723461/50000000000000 : ℝ), (8770298362359/20000000000000 : ℝ), (1647472341601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295422647/10000000000 : ℝ)|^8279 ≤ (21484364723461/50000000000000 : ℝ)^6231
        have hw : |(5295422647/10000000000 : ℝ)|=(5295422647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377095207/10000000000 : ℝ)|^8279 ≤ (8770298362359/20000000000000 : ℝ)^6231
        have hw : |(5377095207/10000000000 : ℝ)|=(5377095207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175800011/10000000000 : ℝ)|^8279 ≤ (1647472341601/12500000000000 : ℝ)^6231
        have hw : |(-2175800011/10000000000 : ℝ)|=(2175800011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1120196797/2500000000 : ℝ)*x 0 + (216034557/500000000 : ℝ)*x 1 + (4320691831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120196797/2500000000 : ℝ)^8279 ≤ (17208053343397/50000000000000 : ℝ)^6231 := by
    have hnat : (1120196797 : ℕ)^8279*50000000000000^6231 ≤ 17208053343397^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120196797 2500000000 17208053343397 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216034557/500000000 : ℝ)^8279 ≤ (32791943164857/100000000000000 : ℝ)^6231 := by
    have hnat : (216034557 : ℕ)^8279*100000000000000^6231 ≤ 32791943164857^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216034557 500000000 32791943164857 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4320691831/10000000000 : ℝ)^8279 ≤ (32791950132921/100000000000000 : ℝ)^6231 := by
    have hnat : (4320691831 : ℕ)^8279*100000000000000^6231 ≤ 32791950132921^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320691831 10000000000 32791950132921 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120196797/2500000000 : ℝ), (216034557/500000000 : ℝ), (4320691831/10000000000 : ℝ)] ![(17208053343397/50000000000000 : ℝ), (32791943164857/100000000000000 : ℝ), (32791950132921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120196797/2500000000 : ℝ)|^8279 ≤ (17208053343397/50000000000000 : ℝ)^6231
        have hw : |(1120196797/2500000000 : ℝ)|=(1120196797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216034557/500000000 : ℝ)|^8279 ≤ (32791943164857/100000000000000 : ℝ)^6231
        have hw : |(216034557/500000000 : ℝ)|=(216034557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4320691831/10000000000 : ℝ)|^8279 ≤ (32791950132921/100000000000000 : ℝ)^6231
        have hw : |(4320691831/10000000000 : ℝ)|=(4320691831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-72628891/312500000 : ℝ)*x 0 + (5280380983/10000000000 : ℝ)*x 1 + (2640190457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72628891/312500000 : ℝ)^8279 ≤ (14386728387089/100000000000000 : ℝ)^6231 := by
    have hnat : (72628891 : ℕ)^8279*100000000000000^6231 ≤ 14386728387089^6231*312500000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72628891 312500000 14386728387089 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280380983/10000000000 : ℝ)^8279 ≤ (21403318087263/50000000000000 : ℝ)^6231 := by
    have hnat : (5280380983 : ℕ)^8279*50000000000000^6231 ≤ 21403318087263^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280380983 10000000000 21403318087263 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640190457/5000000000 : ℝ)^8279 ≤ (4280663543131/10000000000000 : ℝ)^6231 := by
    have hnat : (2640190457 : ℕ)^8279*10000000000000^6231 ≤ 4280663543131^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640190457 5000000000 4280663543131 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72628891/312500000 : ℝ), (5280380983/10000000000 : ℝ), (2640190457/5000000000 : ℝ)] ![(14386728387089/100000000000000 : ℝ), (21403318087263/50000000000000 : ℝ), (4280663543131/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72628891/312500000 : ℝ)|^8279 ≤ (14386728387089/100000000000000 : ℝ)^6231
        have hw : |(-72628891/312500000 : ℝ)|=(72628891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280380983/10000000000 : ℝ)|^8279 ≤ (21403318087263/50000000000000 : ℝ)^6231
        have hw : |(5280380983/10000000000 : ℝ)|=(5280380983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640190457/5000000000 : ℝ)|^8279 ≤ (4280663543131/10000000000000 : ℝ)^6231
        have hw : |(2640190457/5000000000 : ℝ)|=(2640190457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363837537/10000000000 : ℝ)*x 0 + (-1106836833/5000000000 : ℝ)*x 1 + (660047627/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363837537/10000000000 : ℝ)^8279 ≤ (10926973495497/25000000000000 : ℝ)^6231 := by
    have hnat : (5363837537 : ℕ)^8279*25000000000000^6231 ≤ 10926973495497^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363837537 10000000000 10926973495497 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106836833/5000000000 : ℝ)^8279 ≤ (13485469472477/100000000000000 : ℝ)^6231 := by
    have hnat : (1106836833 : ℕ)^8279*100000000000000^6231 ≤ 13485469472477^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106836833 5000000000 13485469472477 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660047627/1250000000 : ℝ)^8279 ≤ (42806636529977/100000000000000 : ℝ)^6231 := by
    have hnat : (660047627 : ℕ)^8279*100000000000000^6231 ≤ 42806636529977^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660047627 1250000000 42806636529977 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363837537/10000000000 : ℝ), (-1106836833/5000000000 : ℝ), (660047627/1250000000 : ℝ)] ![(10926973495497/25000000000000 : ℝ), (13485469472477/100000000000000 : ℝ), (42806636529977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363837537/10000000000 : ℝ)|^8279 ≤ (10926973495497/25000000000000 : ℝ)^6231
        have hw : |(5363837537/10000000000 : ℝ)|=(5363837537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106836833/5000000000 : ℝ)|^8279 ≤ (13485469472477/100000000000000 : ℝ)^6231
        have hw : |(-1106836833/5000000000 : ℝ)|=(1106836833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660047627/1250000000 : ℝ)|^8279 ≤ (42806636529977/100000000000000 : ℝ)^6231
        have hw : |(660047627/1250000000 : ℝ)|=(660047627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681918749/5000000000 : ℝ)*x 0 + (5280381111/10000000000 : ℝ)*x 1 + (-276709199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681918749/5000000000 : ℝ)^8279 ≤ (43707893559739/100000000000000 : ℝ)^6231 := by
    have hnat : (2681918749 : ℕ)^8279*100000000000000^6231 ≤ 43707893559739^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681918749 5000000000 43707893559739 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280381111/10000000000 : ℝ)^8279 ≤ (21403318776623/50000000000000 : ℝ)^6231 := by
    have hnat : (5280381111 : ℕ)^8279*50000000000000^6231 ≤ 21403318776623^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280381111 10000000000 21403318776623 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276709199/1250000000 : ℝ)^8279 ≤ (3371367218377/25000000000000 : ℝ)^6231 := by
    have hnat : (276709199 : ℕ)^8279*25000000000000^6231 ≤ 3371367218377^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276709199 1250000000 3371367218377 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681918749/5000000000 : ℝ), (5280381111/10000000000 : ℝ), (-276709199/1250000000 : ℝ)] ![(43707893559739/100000000000000 : ℝ), (21403318776623/50000000000000 : ℝ), (3371367218377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681918749/5000000000 : ℝ)|^8279 ≤ (43707893559739/100000000000000 : ℝ)^6231
        have hw : |(2681918749/5000000000 : ℝ)|=(2681918749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280381111/10000000000 : ℝ)|^8279 ≤ (21403318776623/50000000000000 : ℝ)^6231
        have hw : |(5280381111/10000000000 : ℝ)|=(5280381111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276709199/1250000000 : ℝ)|^8279 ≤ (3371367218377/25000000000000 : ℝ)^6231
        have hw : |(-276709199/1250000000 : ℝ)|=(276709199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4264124941/10000000000 : ℝ)*x 0 + (4429001201/10000000000 : ℝ)*x 1 + (4429001431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4264124941/10000000000 : ℝ)^8279 ≤ (3222275888227/10000000000000 : ℝ)^6231 := by
    have hnat : (4264124941 : ℕ)^8279*10000000000000^6231 ≤ 3222275888227^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264124941 10000000000 3222275888227 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429001201/10000000000 : ℝ)^8279 ≤ (33888619383371/100000000000000 : ℝ)^6231 := by
    have hnat : (4429001201 : ℕ)^8279*100000000000000^6231 ≤ 33888619383371^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429001201 10000000000 33888619383371 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429001431/10000000000 : ℝ)^8279 ≤ (2118038857603/6250000000000 : ℝ)^6231 := by
    have hnat : (4429001431 : ℕ)^8279*6250000000000^6231 ≤ 2118038857603^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429001431 10000000000 2118038857603 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4264124941/10000000000 : ℝ), (4429001201/10000000000 : ℝ), (4429001431/10000000000 : ℝ)] ![(3222275888227/10000000000000 : ℝ), (33888619383371/100000000000000 : ℝ), (2118038857603/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4264124941/10000000000 : ℝ)|^8279 ≤ (3222275888227/10000000000000 : ℝ)^6231
        have hw : |(4264124941/10000000000 : ℝ)|=(4264124941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429001201/10000000000 : ℝ)|^8279 ≤ (33888619383371/100000000000000 : ℝ)^6231
        have hw : |(4429001201/10000000000 : ℝ)|=(4429001201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4429001431/10000000000 : ℝ)|^8279 ≤ (2118038857603/6250000000000 : ℝ)^6231
        have hw : |(4429001431/10000000000 : ℝ)|=(4429001431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_8 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1135021501/5000000000 : ℝ)*x 0 + (32591969/62500000 : ℝ)*x 1 + (5386699079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1135021501/5000000000 : ℝ)^8279 ≤ (13943631347319/100000000000000 : ℝ)^6231 := by
    have hnat : (1135021501 : ℕ)^8279*100000000000000^6231 ≤ 13943631347319^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135021501 5000000000 13943631347319 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32591969/62500000 : ℝ)^8279 ≤ (42100781660949/100000000000000 : ℝ)^6231 := by
    have hnat : (32591969 : ℕ)^8279*100000000000000^6231 ≤ 42100781660949^6231*62500000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32591969 62500000 42100781660949 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386699079/10000000000 : ℝ)^8279 ≤ (21977793487/50000000000 : ℝ)^6231 := by
    have hnat : (5386699079 : ℕ)^8279*50000000000^6231 ≤ 21977793487^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386699079 10000000000 21977793487 50000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1135021501/5000000000 : ℝ), (32591969/62500000 : ℝ), (5386699079/10000000000 : ℝ)] ![(13943631347319/100000000000000 : ℝ), (42100781660949/100000000000000 : ℝ), (21977793487/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1135021501/5000000000 : ℝ)|^8279 ≤ (13943631347319/100000000000000 : ℝ)^6231
        have hw : |(-1135021501/5000000000 : ℝ)|=(1135021501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32591969/62500000 : ℝ)|^8279 ≤ (42100781660949/100000000000000 : ℝ)^6231
        have hw : |(32591969/62500000 : ℝ)|=(32591969/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386699079/10000000000 : ℝ)|^8279 ≤ (21977793487/50000000000 : ℝ)^6231
        have hw : |(5386699079/10000000000 : ℝ)|=(5386699079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_9 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644312547/5000000000 : ℝ)*x 0 + (-21719693/100000000 : ℝ)*x 1 + (5386698907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644312547/5000000000 : ℝ)^8279 ≤ (21447729152171/50000000000000 : ℝ)^6231 := by
    have hnat : (2644312547 : ℕ)^8279*50000000000000^6231 ≤ 21447729152171^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644312547 5000000000 21447729152171 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21719693/100000000 : ℝ)^8279 ≤ (41090489319/312500000000 : ℝ)^6231 := by
    have hnat : (21719693 : ℕ)^8279*312500000000^6231 ≤ 41090489319^6231*100000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21719693 100000000 41090489319 312500000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386698907/10000000000 : ℝ)^8279 ≤ (43955585109167/100000000000000 : ℝ)^6231 := by
    have hnat : (5386698907 : ℕ)^8279*100000000000000^6231 ≤ 43955585109167^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386698907 10000000000 43955585109167 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644312547/5000000000 : ℝ), (-21719693/100000000 : ℝ), (5386698907/10000000000 : ℝ)] ![(21447729152171/50000000000000 : ℝ), (41090489319/312500000000 : ℝ), (43955585109167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644312547/5000000000 : ℝ)|^8279 ≤ (21447729152171/50000000000000 : ℝ)^6231
        have hw : |(2644312547/5000000000 : ℝ)|=(2644312547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21719693/100000000 : ℝ)|^8279 ≤ (41090489319/312500000000 : ℝ)^6231
        have hw : |(-21719693/100000000 : ℝ)|=(21719693/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386698907/10000000000 : ℝ)|^8279 ≤ (43955585109167/100000000000000 : ℝ)^6231
        have hw : |(5386698907/10000000000 : ℝ)|=(5386698907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_10 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288625131/10000000000 : ℝ)*x 0 + (2693349533/5000000000 : ℝ)*x 1 + (-434393807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288625131/10000000000 : ℝ)^8279 ≤ (42895458703083/100000000000000 : ℝ)^6231 := by
    have hnat : (5288625131 : ℕ)^8279*100000000000000^6231 ≤ 42895458703083^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288625131 10000000000 42895458703083 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693349533/5000000000 : ℝ)^8279 ≤ (43955586833053/100000000000000 : ℝ)^6231 := by
    have hnat : (2693349533 : ℕ)^8279*100000000000000^6231 ≤ 43955586833053^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693349533 5000000000 43955586833053 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434393807/2000000000 : ℝ)^8279 ≤ (13148954450491/100000000000000 : ℝ)^6231 := by
    have hnat : (434393807 : ℕ)^8279*100000000000000^6231 ≤ 13148954450491^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434393807 2000000000 13148954450491 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288625131/10000000000 : ℝ), (2693349533/5000000000 : ℝ), (-434393807/2000000000 : ℝ)] ![(42895458703083/100000000000000 : ℝ), (43955586833053/100000000000000 : ℝ), (13148954450491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288625131/10000000000 : ℝ)|^8279 ≤ (42895458703083/100000000000000 : ℝ)^6231
        have hw : |(5288625131/10000000000 : ℝ)|=(5288625131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693349533/5000000000 : ℝ)|^8279 ≤ (43955586833053/100000000000000 : ℝ)^6231
        have hw : |(2693349533/5000000000 : ℝ)|=(2693349533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434393807/2000000000 : ℝ)|^8279 ≤ (13148954450491/100000000000000 : ℝ)^6231
        have hw : |(-434393807/2000000000 : ℝ)|=(434393807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_11 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4502028123/10000000000 : ℝ)*x 0 + (430993031/1000000000 : ℝ)*x 1 + (4309930651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4502028123/10000000000 : ℝ)^8279 ≤ (4329130797849/12500000000000 : ℝ)^6231 := by
    have hnat : (4502028123 : ℕ)^8279*12500000000000^6231 ≤ 4329130797849^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502028123 10000000000 4329130797849 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430993031/1000000000 : ℝ)^8279 ≤ (32683475087401/100000000000000 : ℝ)^6231 := by
    have hnat : (430993031 : ℕ)^8279*100000000000000^6231 ≤ 32683475087401^6231*1000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430993031 1000000000 32683475087401 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4309930651/10000000000 : ℝ)^8279 ≤ (16341739261619/50000000000000 : ℝ)^6231 := by
    have hnat : (4309930651 : ℕ)^8279*50000000000000^6231 ≤ 16341739261619^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309930651 10000000000 16341739261619 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4502028123/10000000000 : ℝ), (430993031/1000000000 : ℝ), (4309930651/10000000000 : ℝ)] ![(4329130797849/12500000000000 : ℝ), (32683475087401/100000000000000 : ℝ), (16341739261619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4502028123/10000000000 : ℝ)|^8279 ≤ (4329130797849/12500000000000 : ℝ)^6231
        have hw : |(4502028123/10000000000 : ℝ)|=(4502028123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430993031/1000000000 : ℝ)|^8279 ≤ (32683475087401/100000000000000 : ℝ)^6231
        have hw : |(430993031/1000000000 : ℝ)|=(430993031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4309930651/10000000000 : ℝ)|^8279 ≤ (16341739261619/50000000000000 : ℝ)^6231
        have hw : |(4309930651/10000000000 : ℝ)|=(4309930651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_12 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119619039/10000000000 : ℝ)*x 0 + (5441441403/10000000000 : ℝ)*x 1 + (329523087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119619039/10000000000 : ℝ)^8279 ≤ (12729542010619/100000000000000 : ℝ)^6231 := by
    have hnat : (2119619039 : ℕ)^8279*100000000000000^6231 ≤ 12729542010619^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119619039 10000000000 12729542010619 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441441403/10000000000 : ℝ)^8279 ≤ (44550095109371/100000000000000 : ℝ)^6231 := by
    have hnat : (5441441403 : ℕ)^8279*100000000000000^6231 ≤ 44550095109371^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441441403 10000000000 44550095109371 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329523087/625000000 : ℝ)^8279 ≤ (42720362875327/100000000000000 : ℝ)^6231 := by
    have hnat : (329523087 : ℕ)^8279*100000000000000^6231 ≤ 42720362875327^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329523087 625000000 42720362875327 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119619039/10000000000 : ℝ), (5441441403/10000000000 : ℝ), (329523087/625000000 : ℝ)] ![(12729542010619/100000000000000 : ℝ), (44550095109371/100000000000000 : ℝ), (42720362875327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119619039/10000000000 : ℝ)|^8279 ≤ (12729542010619/100000000000000 : ℝ)^6231
        have hw : |(-2119619039/10000000000 : ℝ)|=(2119619039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441441403/10000000000 : ℝ)|^8279 ≤ (44550095109371/100000000000000 : ℝ)^6231
        have hw : |(5441441403/10000000000 : ℝ)|=(5441441403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329523087/625000000 : ℝ)|^8279 ≤ (42720362875327/100000000000000 : ℝ)^6231
        have hw : |(329523087/625000000 : ℝ)|=(329523087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_13 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369502621/10000000000 : ℝ)*x 0 + (-1108376307/5000000000 : ℝ)*x 1 + (5272369433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369502621/10000000000 : ℝ)^8279 ≤ (43769239961717/100000000000000 : ℝ)^6231 := by
    have hnat : (5369502621 : ℕ)^8279*100000000000000^6231 ≤ 43769239961717^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369502621 10000000000 43769239961717 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108376307/5000000000 : ℝ)^8279 ≤ (13510396711853/100000000000000 : ℝ)^6231 := by
    have hnat : (1108376307 : ℕ)^8279*100000000000000^6231 ≤ 13510396711853^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108376307 5000000000 13510396711853 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272369433/10000000000 : ℝ)^8279 ≤ (5340045414591/12500000000000 : ℝ)^6231 := by
    have hnat : (5272369433 : ℕ)^8279*12500000000000^6231 ≤ 5340045414591^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272369433 10000000000 5340045414591 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369502621/10000000000 : ℝ), (-1108376307/5000000000 : ℝ), (5272369433/10000000000 : ℝ)] ![(43769239961717/100000000000000 : ℝ), (13510396711853/100000000000000 : ℝ), (5340045414591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369502621/10000000000 : ℝ)|^8279 ≤ (43769239961717/100000000000000 : ℝ)^6231
        have hw : |(5369502621/10000000000 : ℝ)|=(5369502621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1108376307/5000000000 : ℝ)|^8279 ≤ (13510396711853/100000000000000 : ℝ)^6231
        have hw : |(-1108376307/5000000000 : ℝ)|=(1108376307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272369433/10000000000 : ℝ)|^8279 ≤ (5340045414591/12500000000000 : ℝ)^6231
        have hw : |(5272369433/10000000000 : ℝ)|=(5272369433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_14 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369502519/10000000000 : ℝ)*x 0 + (5272369581/10000000000 : ℝ)*x 1 + (-1108376277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369502519/10000000000 : ℝ)^8279 ≤ (43769238856989/100000000000000 : ℝ)^6231 := by
    have hnat : (5369502519 : ℕ)^8279*100000000000000^6231 ≤ 43769238856989^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369502519 10000000000 43769238856989 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272369581/10000000000 : ℝ)^8279 ≤ (42720364910077/100000000000000 : ℝ)^6231 := by
    have hnat : (5272369581 : ℕ)^8279*100000000000000^6231 ≤ 42720364910077^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272369581 10000000000 42720364910077 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108376277/5000000000 : ℝ)^8279 ≤ (13510396225981/100000000000000 : ℝ)^6231 := by
    have hnat : (1108376277 : ℕ)^8279*100000000000000^6231 ≤ 13510396225981^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108376277 5000000000 13510396225981 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369502519/10000000000 : ℝ), (5272369581/10000000000 : ℝ), (-1108376277/5000000000 : ℝ)] ![(43769238856989/100000000000000 : ℝ), (42720364910077/100000000000000 : ℝ), (13510396225981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369502519/10000000000 : ℝ)|^8279 ≤ (43769238856989/100000000000000 : ℝ)^6231
        have hw : |(5369502519/10000000000 : ℝ)|=(5369502519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272369581/10000000000 : ℝ)|^8279 ≤ (42720364910077/100000000000000 : ℝ)^6231
        have hw : |(5272369581/10000000000 : ℝ)|=(5272369581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108376277/5000000000 : ℝ)|^8279 ≤ (13510396225981/100000000000000 : ℝ)^6231
        have hw : |(-1108376277/5000000000 : ℝ)|=(1108376277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_box_15 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (849189233/2000000000 : ℝ)*x 0 + (4437968917/10000000000 : ℝ)*x 1 + (1109492167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849189233/2000000000 : ℝ)^8279 ≤ (32040363894033/100000000000000 : ℝ)^6231 := by
    have hnat : (849189233 : ℕ)^8279*100000000000000^6231 ≤ 32040363894033^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849189233 2000000000 32040363894033 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4437968917/10000000000 : ℝ)^8279 ≤ (6795963861523/20000000000000 : ℝ)^6231 := by
    have hnat : (4437968917 : ℕ)^8279*20000000000000^6231 ≤ 6795963861523^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437968917 10000000000 6795963861523 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109492167/2500000000 : ℝ)^8279 ≤ (8494954193623/25000000000000 : ℝ)^6231 := by
    have hnat : (1109492167 : ℕ)^8279*25000000000000^6231 ≤ 8494954193623^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109492167 2500000000 8494954193623 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849189233/2000000000 : ℝ), (4437968917/10000000000 : ℝ), (1109492167/2500000000 : ℝ)] ![(32040363894033/100000000000000 : ℝ), (6795963861523/20000000000000 : ℝ), (8494954193623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849189233/2000000000 : ℝ)|^8279 ≤ (32040363894033/100000000000000 : ℝ)^6231
        have hw : |(849189233/2000000000 : ℝ)|=(849189233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4437968917/10000000000 : ℝ)|^8279 ≤ (6795963861523/20000000000000 : ℝ)^6231
        have hw : |(4437968917/10000000000 : ℝ)|=(4437968917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1109492167/2500000000 : ℝ)|^8279 ≤ (8494954193623/25000000000000 : ℝ)^6231
        have hw : |(1109492167/2500000000 : ℝ)|=(1109492167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31113/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7407/12500 : ℝ) ∧ (15927/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41499/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (14766757937843357/100000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^4139 ≤ (14766757937843357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11279 : ℕ)^4139*100000000000000000000^1024 ≤ 14766757937843357^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 14766757937843357 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (14766757937843357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2803/20000 : ℝ) ^ (4139/1024 : ℝ) ≤ (1421006214522261/4000000000000000000 : ℝ) := by
    have hpowers : (2803/20000 : ℝ)^4139 ≤ (1421006214522261/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2803 : ℕ)^4139*4000000000000000000^1024 ≤ 1421006214522261^1024*20000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2803 20000 1421006214522261 4000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2803/20000 : ℝ)) (X := (1421006214522261/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014766757937843357/50000000000000000000 : ℝ) ≤ (10000730586129017/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50014766757937843357/50000000000000000000 : ℝ)^1024 ≤ (10000730586129017/10000000000000000 : ℝ)^4139 := by
      have hnat : (50014766757937843357 : ℕ)^1024*10000000000000000^4139 ≤ 10000730586129017^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014766757937843357 50000000000000000000 10000730586129017 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000730586129017/10000000000000000 : ℝ)) (X := (50014766757937843357/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025145956650449941/50000000000000000000 : ℝ) ≤ (1000124400038721/1000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50025145956650449941/50000000000000000000 : ℝ)^1024 ≤ (1000124400038721/1000000000000000 : ℝ)^4139 := by
      have hnat : (50025145956650449941 : ℕ)^1024*1000000000000000^4139 ≤ 1000124400038721^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025145956650449941 50000000000000000000 1000124400038721 1000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000124400038721/1000000000000000 : ℝ)) (X := (50025145956650449941/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001421006214522261/2000000000000000000 : ℝ) ≤ (10001757414645403/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (2001421006214522261/2000000000000000000 : ℝ)^1024 ≤ (10001757414645403/10000000000000000 : ℝ)^4139 := by
      have hnat : (2001421006214522261 : ℕ)^1024*10000000000000000^4139 ≤ 10001757414645403^4139*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001421006214522261 2000000000000000000 10001757414645403 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001757414645403/10000000000000000 : ℝ)) (X := (2001421006214522261/2000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14766757937843357/100000000000000000000 : ℝ) ≤ ((13675208642406336409/13680000000000000000 : ℝ)+2*(513414258193/273600000000000 : ℝ)*(11279/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (13675208642406336409/13680000000000000000 : ℝ)+2*(513414258193/273600000000000 : ℝ)*(11279/100000 : ℝ)=(10000730586129017/10000000000000000 : ℝ) by norm_num, show 1+2*(14766757937843357/100000000000000000000 : ℝ)=(50014766757937843357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1421006214522261/4000000000000000000 : ℝ)+(14766757937843357/100000000000000000000 : ℝ) ≤ ((13675208642406336409/13680000000000000000 : ℝ)+(513414258193/273600000000000 : ℝ)*((2803/20000 : ℝ)+(11279/100000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (13675208642406336409/13680000000000000000 : ℝ)+(513414258193/273600000000000 : ℝ)*((2803/20000 : ℝ)+(11279/100000 : ℝ))=(1000124400038721/1000000000000000 : ℝ) by norm_num, show 1+(1421006214522261/4000000000000000000 : ℝ)+(14766757937843357/100000000000000000000 : ℝ)=(50025145956650449941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1421006214522261/4000000000000000000 : ℝ) ≤ ((13675208642406336409/13680000000000000000 : ℝ)+2*(513414258193/273600000000000 : ℝ)*(2803/20000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (13675208642406336409/13680000000000000000 : ℝ)+2*(513414258193/273600000000000 : ℝ)*(2803/20000 : ℝ)=(10001757414645403/10000000000000000 : ℝ) by norm_num, show 1+2*(1421006214522261/4000000000000000000 : ℝ)=(2001421006214522261/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13675208642406336409/13680000000000000000 : ℝ)*(X 1 0+X 2 0)+(513414258193/273600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (13675208642406336409/13680000000000000000 : ℝ)) (alpha := (513414258193/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13675208642406336409/13680000000000000000 : ℝ)*(X 0 1+X 2 1)+(513414258193/273600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (13675208642406336409/13680000000000000000 : ℝ)) (alpha := (513414258193/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13675208642406336409/13680000000000000000 : ℝ)*(X 0 2+X 1 2)+(513414258193/273600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (13675208642406336409/13680000000000000000 : ℝ)) (alpha := (513414258193/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129073909/625000000 : ℝ)*X 0 0+(5377095349/10000000000 : ℝ)*X 0 1+(13442739/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647711079/5000000000 : ℝ)*X 1 0+(-1087900039/5000000000 : ℝ)*X 1 1+(5377095643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295422647/10000000000 : ℝ)*X 2 0+(5377095207/10000000000 : ℝ)*X 2 1+(-2175800011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120196797/2500000000 : ℝ)*X 0 0+(216034557/500000000 : ℝ)*X 0 1+(4320691831/10000000000 : ℝ)*X 0 2+(1120196797/2500000000 : ℝ)*X 1 0+(216034557/500000000 : ℝ)*X 1 1+(4320691831/10000000000 : ℝ)*X 1 2+(1120196797/2500000000 : ℝ)*X 2 0+(216034557/500000000 : ℝ)*X 2 1+(4320691831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-72628891/312500000 : ℝ)*X 0 0+(5280380983/10000000000 : ℝ)*X 0 1+(2640190457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363837537/10000000000 : ℝ)*X 1 0+(-1106836833/5000000000 : ℝ)*X 1 1+(660047627/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681918749/5000000000 : ℝ)*X 2 0+(5280381111/10000000000 : ℝ)*X 2 1+(-276709199/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4264124941/10000000000 : ℝ)*X 0 0+(4429001201/10000000000 : ℝ)*X 0 1+(4429001431/10000000000 : ℝ)*X 0 2+(4264124941/10000000000 : ℝ)*X 1 0+(4429001201/10000000000 : ℝ)*X 1 1+(4429001431/10000000000 : ℝ)*X 1 2+(4264124941/10000000000 : ℝ)*X 2 0+(4429001201/10000000000 : ℝ)*X 2 1+(4429001431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1135021501/5000000000 : ℝ)*X 0 0+(32591969/62500000 : ℝ)*X 0 1+(5386699079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644312547/5000000000 : ℝ)*X 1 0+(-21719693/100000000 : ℝ)*X 1 1+(5386698907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288625131/10000000000 : ℝ)*X 2 0+(2693349533/5000000000 : ℝ)*X 2 1+(-434393807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4502028123/10000000000 : ℝ)*X 0 0+(430993031/1000000000 : ℝ)*X 0 1+(4309930651/10000000000 : ℝ)*X 0 2+(4502028123/10000000000 : ℝ)*X 1 0+(430993031/1000000000 : ℝ)*X 1 1+(4309930651/10000000000 : ℝ)*X 1 2+(4502028123/10000000000 : ℝ)*X 2 0+(430993031/1000000000 : ℝ)*X 2 1+(4309930651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2119619039/10000000000 : ℝ)*X 0 0+(5441441403/10000000000 : ℝ)*X 0 1+(329523087/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369502621/10000000000 : ℝ)*X 1 0+(-1108376307/5000000000 : ℝ)*X 1 1+(5272369433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369502519/10000000000 : ℝ)*X 2 0+(5272369581/10000000000 : ℝ)*X 2 1+(-1108376277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((849189233/2000000000 : ℝ)*X 0 0+(4437968917/10000000000 : ℝ)*X 0 1+(1109492167/2500000000 : ℝ)*X 0 2+(849189233/2000000000 : ℝ)*X 1 0+(4437968917/10000000000 : ℝ)*X 1 1+(1109492167/2500000000 : ℝ)*X 1 2+(849189233/2000000000 : ℝ)*X 2 0+(4437968917/10000000000 : ℝ)*X 2 1+(1109492167/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31113/50000 : ℝ) ≤ (-141869231892899477979898299850327/228000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24609181/50000000000000 : ℝ)*(upper0) + (17515473/100000000000000 : ℝ)*(upper1) + (2879397/6250000000000 : ℝ)*(upper3) + (25409569/25000000000000 : ℝ)*(upper5) + (3873382622597903/100000000000000 : ℝ)*(major0) + (3873382622597903/100000000000000 : ℝ)*(major1) + (3873382622597903/100000000000000 : ℝ)*(major2) + (242791141/5000000000000 : ℝ)*(sp3) + (5157095974602409/100000000000000 : ℝ)*(sp4) + (2578549118223677/50000000000000 : ℝ)*(sp5) + (5157062733166663/100000000000000 : ℝ)*(sp6) + (1305201634349719/50000000000000 : ℝ)*(sp7) + (1130922473/50000000000000 : ℝ)*(sp8) + (35503280691/100000000000000 : ℝ)*(sp14) + (1305204062261129/50000000000000 : ℝ)*(f.failure) + (2578549118223677/50000000000000 : ℝ)*(f.sum) + (21685316843039/13680000000000000000000000000 : ℝ)*base65 + (13144665322273300109/456000000000000000000000000000000 : ℝ)*base67 + (8969332774699891/456000000000000000000000000000000 : ℝ)*base70 + (2734219663177300109/456000000000000000000000000000000 : ℝ)*base71 + (55930407443041/13680000000000000000000000000 : ℝ)*base74 + (9431755660198699891/456000000000000000000000000000000 : ℝ)*base76 + (2979564669697300109/456000000000000000000000000000000 : ℝ)*base77 + (7704864769561300109/456000000000000000000000000000000 : ℝ)*base79 + (18644459821439/13680000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2846899/2500000000000000000000 : ℝ)*base89 + (2846899/2500000000000000000000 : ℝ)*base91 + (2846899/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7407/12500 : ℝ) ≤ (2702173800035882413139346371/4560000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64041029/100000000000000 : ℝ)*(lower1) + (206459953/100000000000000 : ℝ)*(lower3) + (36425023/100000000000000 : ℝ)*(upper4) + (69292551/100000000000000 : ℝ)*(upper5) + (3936619582436387/100000000000000 : ℝ)*(major0) + (3936619582436387/100000000000000 : ℝ)*(major1) + (3936619582436387/100000000000000 : ℝ)*(major2) + (1040092141450989/20000000000000 : ℝ)*(sp0) + (5200443669407781/100000000000000 : ℝ)*(sp1) + (520031166394573/10000000000000 : ℝ)*(sp2) + (1326510724628929/50000000000000 : ℝ)*(sp3) + (4259461791/25000000000000 : ℝ)*(sp5) + (4275903541/100000000000000 : ℝ)*(sp7) + (74521654607/50000000000000 : ℝ)*(sp10) + (13265128625807/500000000000 : ℝ)*(f.failure) + (1040092141450989/20000000000000 : ℝ)*(f.sum) + (24172620776291/13680000000000000000000000000 : ℝ)*base65 + (2815924060229645239/456000000000000000000000000000000 : ℝ)*base68 + (21724550249597645239/456000000000000000000000000000000 : ℝ)*base70 + (1689919471410354761/456000000000000000000000000000000 : ℝ)*base71 + (65302532967229/13680000000000000000000000000 : ℝ)*base74 + (29505139081589645239/456000000000000000000000000000000 : ℝ)*base76 + (1503872439042354761/456000000000000000000000000000000 : ℝ)*base77 + (1389600040146354761/456000000000000000000000000000000 : ℝ)*base79 + (1281626804249629/13680000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (367717/25000000000000000000 : ℝ)*base89 + (367717/25000000000000000000 : ℝ)*base91 + (367717/25000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (15927/20000 : ℝ) ≤ (3026222076578691489326511881601/3800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101315981/100000000000000 : ℝ)*(upper0) + (10637163/10000000000000 : ℝ)*(lower3) + (106019271/100000000000000 : ℝ)*(upper4) + (440479433465667/10000000000000 : ℝ)*(major0) + (440479433465667/10000000000000 : ℝ)*(major1) + (440479433465667/10000000000000 : ℝ)*(major2) + (7680700177/20000000000000 : ℝ)*(sp1) + (162719344201/100000000000000 : ℝ)*(sp2) + (54158445621/100000000000000 : ℝ)*(sp3) + (2870405769/100000000000000 : ℝ)*(sp4) + (5814494913602009/100000000000000 : ℝ)*(sp8) + (5814459380506893/100000000000000 : ℝ)*(sp9) + (5814335064663577/100000000000000 : ℝ)*(sp10) + (593698183834129/20000000000000 : ℝ)*(sp11) + (1484272538808133/50000000000000 : ℝ)*(f.failure) + (2907248892003889/50000000000000 : ℝ)*(f.sum) + (120998645273/30400000000000000000000000 : ℝ)*base66 + (204947032874831133/15200000000000000000000000000000 : ℝ)*base68 + (32091878134031133/15200000000000000000000000000000 : ℝ)*base70 + (182277474380431133/15200000000000000000000000000000 : ℝ)*base72 + (2321167646939/152000000000000000000000000 : ℝ)*base73 + (1450456945168867/15200000000000000000000000000000 : ℝ)*base75 + (188124775482831133/15200000000000000000000000000000 : ℝ)*base78 + (298926465385231133/15200000000000000000000000000000 : ℝ)*base80 + (249613822779/152000000000000000000000000 : ℝ)*base81 + (29268423/2500000000000000000000 : ℝ)*base89 + (29268423/2500000000000000000000 : ℝ)*base91 + (29268423/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41499/50000 : ℝ) ≤ (-3942291938594782373569993409903/4750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77512603/100000000000000 : ℝ)*(lower0) + (4342779/5000000000000 : ℝ)*(upper3) + (23143749/25000000000000 : ℝ)*(upper5) + (277464831523701/6250000000000 : ℝ)*(major0) + (277464831523701/6250000000000 : ℝ)*(major1) + (277464831523701/6250000000000 : ℝ)*(major2) + (5171066771/50000000000000 : ℝ)*(sp4) + (5324669991/5000000000000 : ℝ)*(sp5) + (121043867227/100000000000000 : ℝ)*(sp7) + (1261870247/100000000000000 : ℝ)*(sp8) + (2957318011932271/50000000000000 : ℝ)*(sp12) + (5914541134468511/100000000000000 : ℝ)*(sp13) + (5914647627868331/100000000000000 : ℝ)*(sp14) + (1495885571804739/50000000000000 : ℝ)*(sp15) + (598378437495341/20000000000000 : ℝ)*(f.failure) + (5914647627868331/100000000000000 : ℝ)*(f.sum) + (75221155123/142500000000000000000000000 : ℝ)*base65 + (610751109063346699/9500000000000000000000000000000 : ℝ)*base68 + (245531947057153301/9500000000000000000000000000000 : ℝ)*base69 + (72992798458153301/9500000000000000000000000000000 : ℝ)*base71 + (6264755072521/71250000000000000000000000 : ℝ)*base74 + (211522678386153301/9500000000000000000000000000000 : ℝ)*base75 + (97851304837153301/9500000000000000000000000000000 : ℝ)*base77 + (201800431143846699/9500000000000000000000000000000 : ℝ)*base80 + (38489226541/71250000000000000000000000 : ℝ)*base82 + (3979329/1000000000000000000000 : ℝ)*base90 + (3979329/1000000000000000000000 : ℝ)*base92 + (3979329/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1086_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7407/12500 : ℝ) else (15927/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41499/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1086_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1086_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7407/12500 : ℝ) else (15927/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41499/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1086_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7407/12500 : ℝ) else (15927/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41499/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

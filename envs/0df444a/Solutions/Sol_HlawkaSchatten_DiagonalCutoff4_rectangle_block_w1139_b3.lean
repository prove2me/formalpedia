-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1139_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:53.424007+00:00
-- url     : https://prove2.me/submissions/409d90fb-b05c-454d-b815-f62d891c1d20

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
theorem support_rectangle_w1139_box_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1020663407/5000000000 : ℝ)*x 0 + (5376354619/10000000000 : ℝ)*x 1 + (5376354507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020663407/5000000000 : ℝ)^2083 ≤ (2432417711323/20000000000000 : ℝ)^1571 := by
    have hnat : (1020663407 : ℕ)^2083*20000000000000^1571 ≤ 2432417711323^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020663407 5000000000 2432417711323 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376354619/10000000000 : ℝ)^2083 ≤ (21959478162303/50000000000000 : ℝ)^1571 := by
    have hnat : (5376354619 : ℕ)^2083*50000000000000^1571 ≤ 21959478162303^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376354619 10000000000 21959478162303 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376354507/10000000000 : ℝ)^2083 ≤ (4391895511151/10000000000000 : ℝ)^1571 := by
    have hnat : (5376354507 : ℕ)^2083*10000000000000^1571 ≤ 4391895511151^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376354507 10000000000 4391895511151 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1020663407/5000000000 : ℝ), (5376354619/10000000000 : ℝ), (5376354507/10000000000 : ℝ)] ![(2432417711323/20000000000000 : ℝ), (21959478162303/50000000000000 : ℝ), (4391895511151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1020663407/5000000000 : ℝ)|^2083 ≤ (2432417711323/20000000000000 : ℝ)^1571
        have hw : |(-1020663407/5000000000 : ℝ)|=(1020663407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376354619/10000000000 : ℝ)|^2083 ≤ (21959478162303/50000000000000 : ℝ)^1571
        have hw : |(5376354619/10000000000 : ℝ)|=(5376354619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376354507/10000000000 : ℝ)|^2083 ≤ (4391895511151/10000000000000 : ℝ)^1571
        have hw : |(5376354507/10000000000 : ℝ)|=(5376354507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5295956371/10000000000 : ℝ)*x 0 + (-2150353331/10000000000 : ℝ)*x 1 + (1344088641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295956371/10000000000 : ℝ)^2083 ≤ (43050274768731/100000000000000 : ℝ)^1571 := by
    have hnat : (5295956371 : ℕ)^2083*100000000000000^1571 ≤ 43050274768731^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295956371 10000000000 43050274768731 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150353331/10000000000 : ℝ)^2083 ≤ (651538474171/5000000000000 : ℝ)^1571 := by
    have hnat : (2150353331 : ℕ)^2083*5000000000000^1571 ≤ 651538474171^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150353331 10000000000 651538474171 5000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344088641/2500000000 : ℝ)^2083 ≤ (43918955728889/100000000000000 : ℝ)^1571 := by
    have hnat : (1344088641 : ℕ)^2083*100000000000000^1571 ≤ 43918955728889^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344088641 2500000000 43918955728889 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295956371/10000000000 : ℝ), (-2150353331/10000000000 : ℝ), (1344088641/2500000000 : ℝ)] ![(43050274768731/100000000000000 : ℝ), (651538474171/5000000000000 : ℝ), (43918955728889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295956371/10000000000 : ℝ)|^2083 ≤ (43050274768731/100000000000000 : ℝ)^1571
        have hw : |(5295956371/10000000000 : ℝ)|=(5295956371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2150353331/10000000000 : ℝ)|^2083 ≤ (651538474171/5000000000000 : ℝ)^1571
        have hw : |(-2150353331/10000000000 : ℝ)|=(2150353331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344088641/2500000000 : ℝ)|^2083 ≤ (43918955728889/100000000000000 : ℝ)^1571
        have hw : |(1344088641/2500000000 : ℝ)|=(1344088641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1323988987/2500000000 : ℝ)*x 0 + (5376354619/10000000000 : ℝ)*x 1 + (-67198557/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323988987/2500000000 : ℝ)^2083 ≤ (4305027020957/10000000000000 : ℝ)^1571 := by
    have hnat : (1323988987 : ℕ)^2083*10000000000000^1571 ≤ 4305027020957^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323988987 2500000000 4305027020957 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376354619/10000000000 : ℝ)^2083 ≤ (21959478162303/50000000000000 : ℝ)^1571 := by
    have hnat : (5376354619 : ℕ)^2083*50000000000000^1571 ≤ 21959478162303^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376354619 10000000000 21959478162303 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67198557/312500000 : ℝ)^2083 ≤ (13030773444561/100000000000000 : ℝ)^1571 := by
    have hnat : (67198557 : ℕ)^2083*100000000000000^1571 ≤ 13030773444561^1571*312500000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67198557 312500000 13030773444561 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323988987/2500000000 : ℝ), (5376354619/10000000000 : ℝ), (-67198557/312500000 : ℝ)] ![(4305027020957/10000000000000 : ℝ), (21959478162303/50000000000000 : ℝ), (13030773444561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323988987/2500000000 : ℝ)|^2083 ≤ (4305027020957/10000000000000 : ℝ)^1571
        have hw : |(1323988987/2500000000 : ℝ)|=(1323988987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376354619/10000000000 : ℝ)|^2083 ≤ (21959478162303/50000000000000 : ℝ)^1571
        have hw : |(5376354619/10000000000 : ℝ)|=(5376354619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67198557/312500000 : ℝ)|^2083 ≤ (13030773444561/100000000000000 : ℝ)^1571
        have hw : |(-67198557/312500000 : ℝ)|=(67198557/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (223633919/500000000 : ℝ)*x 0 + (2156709149/5000000000 : ℝ)*x 1 + (2156709209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223633919/500000000 : ℝ)^2083 ≤ (34410042177881/100000000000000 : ℝ)^1571 := by
    have hnat : (223633919 : ℕ)^2083*100000000000000^1571 ≤ 34410042177881^1571*500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223633919 500000000 34410042177881 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156709149/5000000000 : ℝ)^2083 ≤ (32794978298957/100000000000000 : ℝ)^1571 := by
    have hnat : (2156709149 : ℕ)^2083*100000000000000^1571 ≤ 32794978298957^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156709149 5000000000 32794978298957 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156709209/5000000000 : ℝ)^2083 ≤ (4099372438583/12500000000000 : ℝ)^1571 := by
    have hnat : (2156709209 : ℕ)^2083*12500000000000^1571 ≤ 4099372438583^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156709209 5000000000 4099372438583 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223633919/500000000 : ℝ), (2156709149/5000000000 : ℝ), (2156709209/5000000000 : ℝ)] ![(34410042177881/100000000000000 : ℝ), (32794978298957/100000000000000 : ℝ), (4099372438583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223633919/500000000 : ℝ)|^2083 ≤ (34410042177881/100000000000000 : ℝ)^1571
        have hw : |(223633919/500000000 : ℝ)|=(223633919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156709149/5000000000 : ℝ)|^2083 ≤ (32794978298957/100000000000000 : ℝ)^1571
        have hw : |(2156709149/5000000000 : ℝ)|=(2156709149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156709209/5000000000 : ℝ)|^2083 ≤ (4099372438583/12500000000000 : ℝ)^1571
        have hw : |(2156709209/5000000000 : ℝ)|=(2156709209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-287088181/1250000000 : ℝ)*x 0 + (2640550729/5000000000 : ℝ)*x 1 + (660137671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287088181/1250000000 : ℝ)^2083 ≤ (1421952220949/10000000000000 : ℝ)^1571 := by
    have hnat : (287088181 : ℕ)^2083*10000000000000^1571 ≤ 1421952220949^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287088181 1250000000 1421952220949 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640550729/5000000000 : ℝ)^2083 ≤ (42890239372371/100000000000000 : ℝ)^1571 := by
    have hnat : (2640550729 : ℕ)^2083*100000000000000^1571 ≤ 42890239372371^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640550729 5000000000 42890239372371 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660137671/1250000000 : ℝ)^2083 ≤ (5361279800403/12500000000000 : ℝ)^1571 := by
    have hnat : (660137671 : ℕ)^2083*12500000000000^1571 ≤ 5361279800403^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660137671 1250000000 5361279800403 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287088181/1250000000 : ℝ), (2640550729/5000000000 : ℝ), (660137671/1250000000 : ℝ)] ![(1421952220949/10000000000000 : ℝ), (42890239372371/100000000000000 : ℝ), (5361279800403/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287088181/1250000000 : ℝ)|^2083 ≤ (1421952220949/10000000000000 : ℝ)^1571
        have hw : |(-287088181/1250000000 : ℝ)|=(287088181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640550729/5000000000 : ℝ)|^2083 ≤ (42890239372371/100000000000000 : ℝ)^1571
        have hw : |(2640550729/5000000000 : ℝ)|=(2640550729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660137671/1250000000 : ℝ)|^2083 ≤ (5361279800403/12500000000000 : ℝ)^1571
        have hw : |(660137671/1250000000 : ℝ)|=(660137671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681628503/5000000000 : ℝ)*x 0 + (-2187814449/10000000000 : ℝ)*x 1 + (2640550683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681628503/5000000000 : ℝ)^2083 ≤ (10944287401409/25000000000000 : ℝ)^1571 := by
    have hnat : (2681628503 : ℕ)^2083*25000000000000^1571 ≤ 10944287401409^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681628503 5000000000 10944287401409 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187814449/10000000000 : ℝ)^2083 ≤ (3333152998779/25000000000000 : ℝ)^1571 := by
    have hnat : (2187814449 : ℕ)^2083*25000000000000^1571 ≤ 3333152998779^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187814449 10000000000 3333152998779 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640550683/5000000000 : ℝ)^2083 ≤ (5361279797711/12500000000000 : ℝ)^1571 := by
    have hnat : (2640550683 : ℕ)^2083*12500000000000^1571 ≤ 5361279797711^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640550683 5000000000 5361279797711 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681628503/5000000000 : ℝ), (-2187814449/10000000000 : ℝ), (2640550683/5000000000 : ℝ)] ![(10944287401409/25000000000000 : ℝ), (3333152998779/25000000000000 : ℝ), (5361279797711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681628503/5000000000 : ℝ)|^2083 ≤ (10944287401409/25000000000000 : ℝ)^1571
        have hw : |(2681628503/5000000000 : ℝ)|=(2681628503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187814449/10000000000 : ℝ)|^2083 ≤ (3333152998779/25000000000000 : ℝ)^1571
        have hw : |(-2187814449/10000000000 : ℝ)|=(2187814449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640550683/5000000000 : ℝ)|^2083 ≤ (5361279797711/12500000000000 : ℝ)^1571
        have hw : |(2640550683/5000000000 : ℝ)|=(2640550683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363257011/10000000000 : ℝ)*x 0 + (5281101423/10000000000 : ℝ)*x 1 + (-1093907183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363257011/10000000000 : ℝ)^2083 ≤ (43777149659749/100000000000000 : ℝ)^1571 := by
    have hnat : (5363257011 : ℕ)^2083*100000000000000^1571 ≤ 43777149659749^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363257011 10000000000 43777149659749 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281101423/10000000000 : ℝ)^2083 ≤ (42890238995481/100000000000000 : ℝ)^1571 := by
    have hnat : (5281101423 : ℕ)^2083*100000000000000^1571 ≤ 42890238995481^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281101423 10000000000 42890238995481 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093907183/5000000000 : ℝ)^2083 ≤ (6666305662233/50000000000000 : ℝ)^1571 := by
    have hnat : (1093907183 : ℕ)^2083*50000000000000^1571 ≤ 6666305662233^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093907183 5000000000 6666305662233 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363257011/10000000000 : ℝ), (5281101423/10000000000 : ℝ), (-1093907183/5000000000 : ℝ)] ![(43777149659749/100000000000000 : ℝ), (42890238995481/100000000000000 : ℝ), (6666305662233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363257011/10000000000 : ℝ)|^2083 ≤ (43777149659749/100000000000000 : ℝ)^1571
        have hw : |(5363257011/10000000000 : ℝ)|=(5363257011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281101423/10000000000 : ℝ)|^2083 ≤ (42890238995481/100000000000000 : ℝ)^1571
        have hw : |(5281101423/10000000000 : ℝ)|=(5281101423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093907183/5000000000 : ℝ)|^2083 ≤ (6666305662233/50000000000000 : ℝ)^1571
        have hw : |(-1093907183/5000000000 : ℝ)|=(1093907183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42571579/100000000 : ℝ)*x 0 + (2210578833/5000000000 : ℝ)*x 1 + (2210578899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42571579/100000000 : ℝ)^2083 ≤ (6445806487191/20000000000000 : ℝ)^1571 := by
    have hnat : (42571579 : ℕ)^2083*20000000000000^1571 ≤ 6445806487191^1571*100000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42571579 100000000 6445806487191 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210578833/5000000000 : ℝ)^2083 ≤ (33885483101427/100000000000000 : ℝ)^1571 := by
    have hnat : (2210578833 : ℕ)^2083*100000000000000^1571 ≤ 33885483101427^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210578833 5000000000 33885483101427 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210578899/5000000000 : ℝ)^2083 ≤ (16942742221423/50000000000000 : ℝ)^1571 := by
    have hnat : (2210578899 : ℕ)^2083*50000000000000^1571 ≤ 16942742221423^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210578899 5000000000 16942742221423 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42571579/100000000 : ℝ), (2210578833/5000000000 : ℝ), (2210578899/5000000000 : ℝ)] ![(6445806487191/20000000000000 : ℝ), (33885483101427/100000000000000 : ℝ), (16942742221423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42571579/100000000 : ℝ)|^2083 ≤ (6445806487191/20000000000000 : ℝ)^1571
        have hw : |(42571579/100000000 : ℝ)|=(42571579/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210578833/5000000000 : ℝ)|^2083 ≤ (33885483101427/100000000000000 : ℝ)^1571
        have hw : |(2210578833/5000000000 : ℝ)|=(2210578833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210578899/5000000000 : ℝ)|^2083 ≤ (16942742221423/50000000000000 : ℝ)^1571
        have hw : |(2210578899/5000000000 : ℝ)|=(2210578899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_8 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1121652609/5000000000 : ℝ)*x 0 + (521632557/1000000000 : ℝ)*x 1 + (2692981719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121652609/5000000000 : ℝ)^2083 ≤ (3445706701231/25000000000000 : ℝ)^1571 := by
    have hnat : (1121652609 : ℕ)^2083*25000000000000^1571 ≤ 3445706701231^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121652609 5000000000 3445706701231 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521632557/1000000000 : ℝ)^2083 ≤ (42194111365679/100000000000000 : ℝ)^1571 := by
    have hnat : (521632557 : ℕ)^2083*100000000000000^1571 ≤ 42194111365679^1571*1000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521632557 1000000000 42194111365679 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692981719/5000000000 : ℝ)^2083 ≤ (550288272631/1250000000000 : ℝ)^1571 := by
    have hnat : (2692981719 : ℕ)^2083*1250000000000^1571 ≤ 550288272631^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692981719 5000000000 550288272631 1250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1121652609/5000000000 : ℝ), (521632557/1000000000 : ℝ), (2692981719/5000000000 : ℝ)] ![(3445706701231/25000000000000 : ℝ), (42194111365679/100000000000000 : ℝ), (550288272631/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1121652609/5000000000 : ℝ)|^2083 ≤ (3445706701231/25000000000000 : ℝ)^1571
        have hw : |(-1121652609/5000000000 : ℝ)|=(1121652609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521632557/1000000000 : ℝ)|^2083 ≤ (42194111365679/100000000000000 : ℝ)^1571
        have hw : |(521632557/1000000000 : ℝ)|=(521632557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692981719/5000000000 : ℝ)|^2083 ≤ (550288272631/1250000000000 : ℝ)^1571
        have hw : |(2692981719/5000000000 : ℝ)|=(2692981719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_9 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289163607/10000000000 : ℝ)*x 0 + (-2146505507/10000000000 : ℝ)*x 1 + (1346490847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289163607/10000000000 : ℝ)^2083 ≤ (42977076580311/100000000000000 : ℝ)^1571 := by
    have hnat : (5289163607 : ℕ)^2083*100000000000000^1571 ≤ 42977076580311^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289163607 10000000000 42977076580311 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146505507/10000000000 : ℝ)^2083 ≤ (519994485207/4000000000000 : ℝ)^1571 := by
    have hnat : (2146505507 : ℕ)^2083*4000000000000^1571 ≤ 519994485207^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146505507 10000000000 519994485207 4000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346490847/2500000000 : ℝ)^2083 ≤ (11005765317151/25000000000000 : ℝ)^1571 := by
    have hnat : (1346490847 : ℕ)^2083*25000000000000^1571 ≤ 11005765317151^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346490847 2500000000 11005765317151 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289163607/10000000000 : ℝ), (-2146505507/10000000000 : ℝ), (1346490847/2500000000 : ℝ)] ![(42977076580311/100000000000000 : ℝ), (519994485207/4000000000000 : ℝ), (11005765317151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289163607/10000000000 : ℝ)|^2083 ≤ (42977076580311/100000000000000 : ℝ)^1571
        have hw : |(5289163607/10000000000 : ℝ)|=(5289163607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146505507/10000000000 : ℝ)|^2083 ≤ (519994485207/4000000000000 : ℝ)^1571
        have hw : |(-2146505507/10000000000 : ℝ)|=(2146505507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346490847/2500000000 : ℝ)|^2083 ≤ (11005765317151/25000000000000 : ℝ)^1571
        have hw : |(1346490847/2500000000 : ℝ)|=(1346490847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_10 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289163627/10000000000 : ℝ)*x 0 + (5385963429/10000000000 : ℝ)*x 1 + (-1073252713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289163627/10000000000 : ℝ)^2083 ≤ (5372134599473/12500000000000 : ℝ)^1571 := by
    have hnat : (5289163627 : ℕ)^2083*12500000000000^1571 ≤ 5372134599473^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289163627 10000000000 5372134599473 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385963429/10000000000 : ℝ)^2083 ≤ (22011530856471/50000000000000 : ℝ)^1571 := by
    have hnat : (5385963429 : ℕ)^2083*50000000000000^1571 ≤ 22011530856471^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385963429 10000000000 22011530856471 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073252713/5000000000 : ℝ)^2083 ≤ (12999861479739/100000000000000 : ℝ)^1571 := by
    have hnat : (1073252713 : ℕ)^2083*100000000000000^1571 ≤ 12999861479739^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073252713 5000000000 12999861479739 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289163627/10000000000 : ℝ), (5385963429/10000000000 : ℝ), (-1073252713/5000000000 : ℝ)] ![(5372134599473/12500000000000 : ℝ), (22011530856471/50000000000000 : ℝ), (12999861479739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289163627/10000000000 : ℝ)|^2083 ≤ (5372134599473/12500000000000 : ℝ)^1571
        have hw : |(5289163627/10000000000 : ℝ)|=(5289163627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385963429/10000000000 : ℝ)|^2083 ≤ (22011530856471/50000000000000 : ℝ)^1571
        have hw : |(5385963429/10000000000 : ℝ)|=(5385963429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073252713/5000000000 : ℝ)|^2083 ≤ (12999861479739/100000000000000 : ℝ)^1571
        have hw : |(-1073252713/5000000000 : ℝ)|=(1073252713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_11 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2247073231/5000000000 : ℝ)*x 0 + (537817963/1250000000 : ℝ)*x 1 + (26890899/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2247073231/5000000000 : ℝ)^2083 ≤ (4328650383139/12500000000000 : ℝ)^1571 := by
    have hnat : (2247073231 : ℕ)^2083*12500000000000^1571 ≤ 4328650383139^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247073231 5000000000 4328650383139 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537817963/1250000000 : ℝ)^2083 ≤ (32685397780253/100000000000000 : ℝ)^1571 := by
    have hnat : (537817963 : ℕ)^2083*100000000000000^1571 ≤ 32685397780253^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537817963 1250000000 32685397780253 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26890899/62500000 : ℝ)^2083 ≤ (16342699575063/50000000000000 : ℝ)^1571 := by
    have hnat : (26890899 : ℕ)^2083*50000000000000^1571 ≤ 16342699575063^1571*62500000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26890899 62500000 16342699575063 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2247073231/5000000000 : ℝ), (537817963/1250000000 : ℝ), (26890899/62500000 : ℝ)] ![(4328650383139/12500000000000 : ℝ), (32685397780253/100000000000000 : ℝ), (16342699575063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2247073231/5000000000 : ℝ)|^2083 ≤ (4328650383139/12500000000000 : ℝ)^1571
        have hw : |(2247073231/5000000000 : ℝ)|=(2247073231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537817963/1250000000 : ℝ)|^2083 ≤ (32685397780253/100000000000000 : ℝ)^1571
        have hw : |(537817963/1250000000 : ℝ)|=(537817963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26890899/62500000 : ℝ)|^2083 ≤ (16342699575063/50000000000000 : ℝ)^1571
        have hw : |(26890899/62500000 : ℝ)|=(26890899/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_12 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095048313/10000000000 : ℝ)*x 0 + (543985023/1000000000 : ℝ)*x 1 + (5273063827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095048313/10000000000 : ℝ)^2083 ≤ (2517655944779/20000000000000 : ℝ)^1571 := by
    have hnat : (2095048313 : ℕ)^2083*20000000000000^1571 ≤ 2517655944779^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095048313 10000000000 2517655944779 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543985023/1000000000 : ℝ)^2083 ≤ (44608011014383/100000000000000 : ℝ)^1571 := by
    have hnat : (543985023 : ℕ)^2083*100000000000000^1571 ≤ 44608011014383^1571*1000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543985023 1000000000 44608011014383 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273063827/10000000000 : ℝ)^2083 ≤ (10700927310947/25000000000000 : ℝ)^1571 := by
    have hnat : (5273063827 : ℕ)^2083*25000000000000^1571 ≤ 10700927310947^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273063827 10000000000 10700927310947 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095048313/10000000000 : ℝ), (543985023/1000000000 : ℝ), (5273063827/10000000000 : ℝ)] ![(2517655944779/20000000000000 : ℝ), (44608011014383/100000000000000 : ℝ), (10700927310947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095048313/10000000000 : ℝ)|^2083 ≤ (2517655944779/20000000000000 : ℝ)^1571
        have hw : |(-2095048313/10000000000 : ℝ)|=(2095048313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543985023/1000000000 : ℝ)|^2083 ≤ (44608011014383/100000000000000 : ℝ)^1571
        have hw : |(543985023/1000000000 : ℝ)|=(543985023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273063827/10000000000 : ℝ)|^2083 ≤ (10700927310947/25000000000000 : ℝ)^1571
        have hw : |(5273063827/10000000000 : ℝ)|=(5273063827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_13 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684466967/5000000000 : ℝ)*x 0 + (-2190918041/10000000000 : ℝ)*x 1 + (329566467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684466967/5000000000 : ℝ)^2083 ≤ (43838599370787/100000000000000 : ℝ)^1571 := by
    have hnat : (2684466967 : ℕ)^2083*100000000000000^1571 ≤ 43838599370787^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684466967 5000000000 43838599370787 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190918041/10000000000 : ℝ)^2083 ≤ (3339423796917/25000000000000 : ℝ)^1571 := by
    have hnat : (2190918041 : ℕ)^2083*25000000000000^1571 ≤ 3339423796917^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190918041 10000000000 3339423796917 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329566467/625000000 : ℝ)^2083 ≤ (2140185271147/5000000000000 : ℝ)^1571 := by
    have hnat : (329566467 : ℕ)^2083*5000000000000^1571 ≤ 2140185271147^1571*625000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329566467 625000000 2140185271147 5000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684466967/5000000000 : ℝ), (-2190918041/10000000000 : ℝ), (329566467/625000000 : ℝ)] ![(43838599370787/100000000000000 : ℝ), (3339423796917/25000000000000 : ℝ), (2140185271147/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684466967/5000000000 : ℝ)|^2083 ≤ (43838599370787/100000000000000 : ℝ)^1571
        have hw : |(2684466967/5000000000 : ℝ)|=(2684466967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190918041/10000000000 : ℝ)|^2083 ≤ (3339423796917/25000000000000 : ℝ)^1571
        have hw : |(-2190918041/10000000000 : ℝ)|=(2190918041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329566467/625000000 : ℝ)|^2083 ≤ (2140185271147/5000000000000 : ℝ)^1571
        have hw : |(329566467/625000000 : ℝ)|=(329566467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_14 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073786733/2000000000 : ℝ)*x 0 + (5273063961/10000000000 : ℝ)*x 1 + (-2190917751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073786733/2000000000 : ℝ)^2083 ≤ (21919298229251/50000000000000 : ℝ)^1571 := by
    have hnat : (1073786733 : ℕ)^2083*50000000000000^1571 ≤ 21919298229251^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073786733 2000000000 21919298229251 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273063961/10000000000 : ℝ)^2083 ≤ (5350463835753/12500000000000 : ℝ)^1571 := by
    have hnat : (5273063961 : ℕ)^2083*12500000000000^1571 ≤ 5350463835753^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273063961 10000000000 5350463835753 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190917751/10000000000 : ℝ)^2083 ≤ (13357692843351/100000000000000 : ℝ)^1571 := by
    have hnat : (2190917751 : ℕ)^2083*100000000000000^1571 ≤ 13357692843351^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190917751 10000000000 13357692843351 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073786733/2000000000 : ℝ), (5273063961/10000000000 : ℝ), (-2190917751/10000000000 : ℝ)] ![(21919298229251/50000000000000 : ℝ), (5350463835753/12500000000000 : ℝ), (13357692843351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073786733/2000000000 : ℝ)|^2083 ≤ (21919298229251/50000000000000 : ℝ)^1571
        have hw : |(1073786733/2000000000 : ℝ)|=(1073786733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273063961/10000000000 : ℝ)|^2083 ≤ (5350463835753/12500000000000 : ℝ)^1571
        have hw : |(5273063961/10000000000 : ℝ)|=(5273063961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190917751/10000000000 : ℝ)|^2083 ≤ (13357692843351/100000000000000 : ℝ)^1571
        have hw : |(-2190917751/10000000000 : ℝ)|=(2190917751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_box_15 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2119370599/5000000000 : ℝ)*x 0 + (443024391/1000000000 : ℝ)*x 1 + (88604877/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119370599/5000000000 : ℝ)^2083 ≤ (16022149417871/50000000000000 : ℝ)^1571 := by
    have hnat : (2119370599 : ℕ)^2083*50000000000000^1571 ≤ 16022149417871^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119370599 5000000000 16022149417871 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443024391/1000000000 : ℝ)^2083 ≤ (1359114035307/4000000000000 : ℝ)^1571 := by
    have hnat : (443024391 : ℕ)^2083*4000000000000^1571 ≤ 1359114035307^1571*1000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443024391 1000000000 1359114035307 4000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88604877/200000000 : ℝ)^2083 ≤ (3397785027253/10000000000000 : ℝ)^1571 := by
    have hnat : (88604877 : ℕ)^2083*10000000000000^1571 ≤ 3397785027253^1571*200000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88604877 200000000 3397785027253 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119370599/5000000000 : ℝ), (443024391/1000000000 : ℝ), (88604877/200000000 : ℝ)] ![(16022149417871/50000000000000 : ℝ), (1359114035307/4000000000000 : ℝ), (3397785027253/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119370599/5000000000 : ℝ)|^2083 ≤ (16022149417871/50000000000000 : ℝ)^1571
        have hw : |(2119370599/5000000000 : ℝ)|=(2119370599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443024391/1000000000 : ℝ)|^2083 ≤ (1359114035307/4000000000000 : ℝ)^1571
        have hw : |(443024391/1000000000 : ℝ)|=(443024391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88604877/200000000 : ℝ)|^2083 ≤ (3397785027253/10000000000000 : ℝ)^1571
        have hw : |(88604877/200000000 : ℝ)|=(88604877/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62231/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1853/3125 : ℝ) ∧ (79799/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41559/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (227/2000 : ℝ) ^ (8331/2048 : ℝ) ≤ (14316767811048591/100000000000000000000 : ℝ) := by
    have hpowers : (227/2000 : ℝ)^8331 ≤ (14316767811048591/100000000000000000000 : ℝ)^2048 := by
      have hnat : (227 : ℕ)^8331*100000000000000000000^2048 ≤ 14316767811048591^2048*2000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 2000 14316767811048591 100000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/2000 : ℝ)) (X := (14316767811048591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (17039227420469989/50000000000000000000 : ℝ) := by
    have hpowers : (14047/100000 : ℝ)^8331 ≤ (17039227420469989/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14047 : ℕ)^8331*50000000000000000000^2048 ≤ 17039227420469989^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 100000 17039227420469989 50000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/100000 : ℝ)) (X := (17039227420469989/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014316767811048591/50000000000000000000 : ℝ) ≤ (10000703818873139/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (50014316767811048591/50000000000000000000 : ℝ)^2048 ≤ (10000703818873139/10000000000000000 : ℝ)^8331 := by
      have hnat : (50014316767811048591 : ℕ)^2048*10000000000000000^8331 ≤ 10000703818873139^8331*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014316767811048591 50000000000000000000 10000703818873139 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000703818873139/10000000000000000 : ℝ)) (X := (50014316767811048591/50000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048395222651988569/100000000000000000000 : ℝ) ≤ (1000118947705871/1000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (100048395222651988569/100000000000000000000 : ℝ)^2048 ≤ (1000118947705871/1000000000000000 : ℝ)^8331 := by
      have hnat : (100048395222651988569 : ℕ)^2048*1000000000000000^8331 ≤ 1000118947705871^8331*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048395222651988569 100000000000000000000 1000118947705871 1000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118947705871/1000000000000000 : ℝ)) (X := (100048395222651988569/100000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017039227420469989/25000000000000000000 : ℝ) ≤ (10001675135244281/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (25017039227420469989/25000000000000000000 : ℝ)^2048 ≤ (10001675135244281/10000000000000000 : ℝ)^8331 := by
      have hnat : (25017039227420469989 : ℕ)^2048*10000000000000000^8331 ≤ 10001675135244281^8331*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017039227420469989 25000000000000000000 10001675135244281 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001675135244281/10000000000000000 : ℝ)) (X := (25017039227420469989/25000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14316767811048591/100000000000000000000 : ℝ) ≤ ((8986957919562798061/8990000000000000000 : ℝ)+2*(161886061857/89900000000000 : ℝ)*(227/2000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (8986957919562798061/8990000000000000000 : ℝ)+2*(161886061857/89900000000000 : ℝ)*(227/2000 : ℝ)=(10000703818873139/10000000000000000 : ℝ) by norm_num, show 1+2*(14316767811048591/100000000000000000000 : ℝ)=(50014316767811048591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17039227420469989/50000000000000000000 : ℝ)+(14316767811048591/100000000000000000000 : ℝ) ≤ ((8986957919562798061/8990000000000000000 : ℝ)+(161886061857/89900000000000 : ℝ)*((14047/100000 : ℝ)+(227/2000 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (8986957919562798061/8990000000000000000 : ℝ)+(161886061857/89900000000000 : ℝ)*((14047/100000 : ℝ)+(227/2000 : ℝ))=(1000118947705871/1000000000000000 : ℝ) by norm_num, show 1+(17039227420469989/50000000000000000000 : ℝ)+(14316767811048591/100000000000000000000 : ℝ)=(100048395222651988569/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17039227420469989/50000000000000000000 : ℝ) ≤ ((8986957919562798061/8990000000000000000 : ℝ)+2*(161886061857/89900000000000 : ℝ)*(14047/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (8986957919562798061/8990000000000000000 : ℝ)+2*(161886061857/89900000000000 : ℝ)*(14047/100000 : ℝ)=(10001675135244281/10000000000000000 : ℝ) by norm_num, show 1+2*(17039227420469989/50000000000000000000 : ℝ)=(25017039227420469989/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8986957919562798061/8990000000000000000 : ℝ)*(X 1 0+X 2 0)+(161886061857/89900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (8986957919562798061/8990000000000000000 : ℝ)) (alpha := (161886061857/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8986957919562798061/8990000000000000000 : ℝ)*(X 0 1+X 2 1)+(161886061857/89900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (8986957919562798061/8990000000000000000 : ℝ)) (alpha := (161886061857/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8986957919562798061/8990000000000000000 : ℝ)*(X 0 2+X 1 2)+(161886061857/89900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (8986957919562798061/8990000000000000000 : ℝ)) (alpha := (161886061857/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1020663407/5000000000 : ℝ)*X 0 0+(5376354619/10000000000 : ℝ)*X 0 1+(5376354507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295956371/10000000000 : ℝ)*X 1 0+(-2150353331/10000000000 : ℝ)*X 1 1+(1344088641/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323988987/2500000000 : ℝ)*X 2 0+(5376354619/10000000000 : ℝ)*X 2 1+(-67198557/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((223633919/500000000 : ℝ)*X 0 0+(2156709149/5000000000 : ℝ)*X 0 1+(2156709209/5000000000 : ℝ)*X 0 2+(223633919/500000000 : ℝ)*X 1 0+(2156709149/5000000000 : ℝ)*X 1 1+(2156709209/5000000000 : ℝ)*X 1 2+(223633919/500000000 : ℝ)*X 2 0+(2156709149/5000000000 : ℝ)*X 2 1+(2156709209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-287088181/1250000000 : ℝ)*X 0 0+(2640550729/5000000000 : ℝ)*X 0 1+(660137671/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681628503/5000000000 : ℝ)*X 1 0+(-2187814449/10000000000 : ℝ)*X 1 1+(2640550683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363257011/10000000000 : ℝ)*X 2 0+(5281101423/10000000000 : ℝ)*X 2 1+(-1093907183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42571579/100000000 : ℝ)*X 0 0+(2210578833/5000000000 : ℝ)*X 0 1+(2210578899/5000000000 : ℝ)*X 0 2+(42571579/100000000 : ℝ)*X 1 0+(2210578833/5000000000 : ℝ)*X 1 1+(2210578899/5000000000 : ℝ)*X 1 2+(42571579/100000000 : ℝ)*X 2 0+(2210578833/5000000000 : ℝ)*X 2 1+(2210578899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1121652609/5000000000 : ℝ)*X 0 0+(521632557/1000000000 : ℝ)*X 0 1+(2692981719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289163607/10000000000 : ℝ)*X 1 0+(-2146505507/10000000000 : ℝ)*X 1 1+(1346490847/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289163627/10000000000 : ℝ)*X 2 0+(5385963429/10000000000 : ℝ)*X 2 1+(-1073252713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2247073231/5000000000 : ℝ)*X 0 0+(537817963/1250000000 : ℝ)*X 0 1+(26890899/62500000 : ℝ)*X 0 2+(2247073231/5000000000 : ℝ)*X 1 0+(537817963/1250000000 : ℝ)*X 1 1+(26890899/62500000 : ℝ)*X 1 2+(2247073231/5000000000 : ℝ)*X 2 0+(537817963/1250000000 : ℝ)*X 2 1+(26890899/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2095048313/10000000000 : ℝ)*X 0 0+(543985023/1000000000 : ℝ)*X 0 1+(5273063827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684466967/5000000000 : ℝ)*X 1 0+(-2190918041/10000000000 : ℝ)*X 1 1+(329566467/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073786733/2000000000 : ℝ)*X 2 0+(5273063961/10000000000 : ℝ)*X 2 1+(-2190917751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2119370599/5000000000 : ℝ)*X 0 0+(443024391/1000000000 : ℝ)*X 0 1+(88604877/200000000 : ℝ)*X 0 2+(2119370599/5000000000 : ℝ)*X 1 0+(443024391/1000000000 : ℝ)*X 1 1+(88604877/200000000 : ℝ)*X 1 2+(2119370599/5000000000 : ℝ)*X 2 0+(443024391/1000000000 : ℝ)*X 2 1+(88604877/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62231/100000 : ℝ) ≤ (-559432132428390172299047517/899000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12132897/25000000000000 : ℝ)*(lower1) + (8352899/10000000000000 : ℝ)*(lower2) + (5097627/50000000000000 : ℝ)*(lower3) + (11546133/25000000000000 : ℝ)*(lower4) + (391785272145823/10000000000000 : ℝ)*(major0) + (391785272145823/10000000000000 : ℝ)*(major1) + (391785272145823/10000000000000 : ℝ)*(major2) + (238294483/4000000000000 : ℝ)*(sp1) + (797331959/100000000000000 : ℝ)*(sp2) + (5234321553099403/100000000000000 : ℝ)*(sp4) + (1308579312872689/25000000000000 : ℝ)*(sp5) + (5234322411520871/100000000000000 : ℝ)*(sp6) + (1311062495089431/50000000000000 : ℝ)*(sp7) + (827876713/50000000000000 : ℝ)*(sp8) + (1311062495089431/50000000000000 : ℝ)*(f.failure) + (523432320885283/10000000000000 : ℝ)*(f.sum) + (326882098281/89900000000000000000000000 : ℝ)*base65 + (662585975933349203/89900000000000000000000000000000 : ℝ)*base67 + (7232028540481549203/89900000000000000000000000000000 : ℝ)*base69 + (328470516049150797/89900000000000000000000000000000 : ℝ)*base72 + (406914001349/179800000000000000000000000 : ℝ)*base73 + (119293237768050797/89900000000000000000000000000000 : ℝ)*base76 + (314417657506049203/89900000000000000000000000000000 : ℝ)*base77 + (130074519900650797/89900000000000000000000000000000 : ℝ)*base80 + (5771487503987/112375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (20608141/2500000000000000000000 : ℝ)*base90 + (20608141/2500000000000000000000 : ℝ)*base92 + (20608141/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1853/3125 : ℝ) ≤ (2665470583200179134907564697/4495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62356559/100000000000000 : ℝ)*(lower0) + (271061647/100000000000000 : ℝ)*(upper2) + (9451227/25000000000000 : ℝ)*(lower4) + (14787449/12500000000000 : ℝ)*(lower5) + (124436337984389/3125000000000 : ℝ)*(major0) + (124436337984389/3125000000000 : ℝ)*(major1) + (124436337984389/3125000000000 : ℝ)*(major2) + (5279118290867267/100000000000000 : ℝ)*(sp0) + (1319778597094017/25000000000000 : ℝ)*(sp1) + (164972721918837/3125000000000 : ℝ)*(sp2) + (1332512687317347/50000000000000 : ℝ)*(sp3) + (12713026717/100000000000000 : ℝ)*(sp5) + (6965988993/100000000000000 : ℝ)*(sp7) + (4405267759/50000000000000 : ℝ)*(sp12) + (2665032340623687/100000000000000 : ℝ)*(f.failure) + (164972721918837/3125000000000 : ℝ)*(f.sum) + (2135649151419/1123750000000000000000000000 : ℝ)*base65 + (225063443935488479/28093750000000000000000000000000 : ℝ)*base67 + (94629797111449021/28093750000000000000000000000000 : ℝ)*base70 + (227902531250707229/28093750000000000000000000000000 : ℝ)*base71 + (43161051444981/4495000000000000000000000000 : ℝ)*base73 + (53743277645230271/28093750000000000000000000000000 : ℝ)*base76 + (52602344721105271/28093750000000000000000000000000 : ℝ)*base78 + (543336585784957229/28093750000000000000000000000000 : ℝ)*base79 + (13860582807/2247500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (12060643/5000000000000000000000 : ℝ)*base89 + (12060643/5000000000000000000000 : ℝ)*base91 + (12060643/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79799/100000 : ℝ) ≤ (179353756921836280111843231271787/224750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22013877/100000000000000 : ℝ)*(upper0) + (59948127/100000000000000 : ℝ)*(lower3) + (5721277/25000000000000 : ℝ)*(upper4) + (2224921805193411/50000000000000 : ℝ)*(major0) + (2224921805193411/50000000000000 : ℝ)*(major1) + (2224921805193411/50000000000000 : ℝ)*(major2) + (10768292731/25000000000000 : ℝ)*(sp1) + (7426377373/12500000000000 : ℝ)*(sp2) + (16996711459/100000000000000 : ℝ)*(sp3) + (208172317/20000000000000 : ℝ)*(sp4) + (5894911946416607/100000000000000 : ℝ)*(sp8) + (5894869914107269/100000000000000 : ℝ)*(sp9) + (736856697032401/12500000000000 : ℝ)*(sp10) + (1489078376870167/50000000000000 : ℝ)*(sp11) + (2978173750451793/100000000000000 : ℝ)*(f.failure) + (368432061704887/6250000000000 : ℝ)*(f.sum) + (1857077515133/561875000000000000000000000 : ℝ)*base65 + (3960126468682476071/449500000000000000000000000000000 : ℝ)*base67 + (2820557786047476071/449500000000000000000000000000000 : ℝ)*base69 + (1952522381520976071/449500000000000000000000000000000 : ℝ)*base71 + (36367571317409/4495000000000000000000000000 : ℝ)*base73 + (720603826171523929/449500000000000000000000000000000 : ℝ)*base76 + (1271786923151476071/449500000000000000000000000000000 : ℝ)*base77 + (512919685213523929/449500000000000000000000000000000 : ℝ)*base80 + (1864403335611/1123750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15757077/5000000000000000000000 : ℝ)*base89 + (15757077/5000000000000000000000 : ℝ)*base91 + (15757077/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41559/50000 : ℝ) ≤ (-93400815045194995772056864896609/112375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12842969/100000000000000 : ℝ)*(lower0) + (36028929/100000000000000 : ℝ)*(lower1) + (40703669/50000000000000 : ℝ)*(lower2) + (2242387859198823/50000000000000 : ℝ)*(major0) + (2242387859198823/50000000000000 : ℝ)*(major1) + (2242387859198823/50000000000000 : ℝ)*(major2) + (1576169157/12500000000000 : ℝ)*(sp0) + (471664930961/100000000000000 : ℝ)*(sp5) + (44161615881/100000000000000 : ℝ)*(sp6) + (9764576173/50000000000000 : ℝ)*(sp7) + (2997845476384021/50000000000000 : ℝ)*(sp12) + (5995231897190337/100000000000000 : ℝ)*(sp13) + (749457425063177/12500000000000 : ℝ)*(sp14) + (750383361133483/25000000000000 : ℝ)*(sp15) + (1500776486843139/50000000000000 : ℝ)*(f.failure) + (5995703562121297/100000000000000 : ℝ)*(f.sum) + (5292821520913/1123750000000000000000000000 : ℝ)*base65 + (1575545267868982203/449500000000000000000000000000000 : ℝ)*base67 + (977604013354017797/449500000000000000000000000000000 : ℝ)*base70 + (2078650489258982203/449500000000000000000000000000000 : ℝ)*base71 + (589293008117/280937500000000000000000000 : ℝ)*base73 + (2682979578477982203/449500000000000000000000000000000 : ℝ)*base75 + (3798589057512482203/449500000000000000000000000000000 : ℝ)*base77 + (9435155112276482203/449500000000000000000000000000000 : ℝ)*base79 + (6546609578463/1123750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (14118129/2500000000000000000000 : ℝ)*base90 + (14118129/2500000000000000000000 : ℝ)*base92 + (14118129/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1139_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1853/3125 : ℝ) else (79799/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41559/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1139_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1139_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1853/3125 : ℝ) else (79799/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41559/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1139_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1853/3125 : ℝ) else (79799/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41559/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1139_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

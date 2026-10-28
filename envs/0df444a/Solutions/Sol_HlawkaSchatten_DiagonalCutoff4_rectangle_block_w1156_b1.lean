-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:54.886496+00:00
-- url     : https://prove2.me/submissions/1086600c-9e9a-4243-bab1-dfe5e2d92712

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
theorem support_rectangle_w1156_s3_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269569821/1250000000 : ℝ)*x 0 + (1356937543/2500000000 : ℝ)*x 1 + (2616691759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269569821/1250000000 : ℝ)^8349 ≤ (13098306906233/100000000000000 : ℝ)^6301 := by
    have hnat : (269569821 : ℕ)^8349*100000000000000^6301 ≤ 13098306906233^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269569821 1250000000 13098306906233 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356937543/2500000000 : ℝ)^8349 ≤ (44500401611147/100000000000000 : ℝ)^6301 := by
    have hnat : (1356937543 : ℕ)^8349*100000000000000^6301 ≤ 44500401611147^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356937543 2500000000 44500401611147 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616691759/5000000000 : ℝ)^8349 ≤ (42401291474401/100000000000000 : ℝ)^6301 := by
    have hnat : (2616691759 : ℕ)^8349*100000000000000^6301 ≤ 42401291474401^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616691759 5000000000 42401291474401 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269569821/1250000000 : ℝ), (1356937543/2500000000 : ℝ), (2616691759/5000000000 : ℝ)] ![(13098306906233/100000000000000 : ℝ), (44500401611147/100000000000000 : ℝ), (42401291474401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269569821/1250000000 : ℝ)|^8349 ≤ (13098306906233/100000000000000 : ℝ)^6301
        have hw : |(-269569821/1250000000 : ℝ)|=(269569821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356937543/2500000000 : ℝ)|^8349 ≤ (44500401611147/100000000000000 : ℝ)^6301
        have hw : |(1356937543/2500000000 : ℝ)|=(1356937543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616691759/5000000000 : ℝ)|^8349 ≤ (42401291474401/100000000000000 : ℝ)^6301
        have hw : |(2616691759/5000000000 : ℝ)|=(2616691759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676729561/5000000000 : ℝ)*x 0 + (-2255882051/10000000000 : ℝ)*x 1 + (5233383331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676729561/5000000000 : ℝ)^8349 ≤ (43695142862127/100000000000000 : ℝ)^6301 := by
    have hnat : (2676729561 : ℕ)^8349*100000000000000^6301 ≤ 43695142862127^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676729561 5000000000 43695142862127 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255882051/10000000000 : ℝ)^8349 ≤ (434486489263/3125000000000 : ℝ)^6301 := by
    have hnat : (2255882051 : ℕ)^8349*3125000000000^6301 ≤ 434486489263^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255882051 10000000000 434486489263 3125000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233383331/10000000000 : ℝ)^8349 ≤ (21200644733433/50000000000000 : ℝ)^6301 := by
    have hnat : (5233383331 : ℕ)^8349*50000000000000^6301 ≤ 21200644733433^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233383331 10000000000 21200644733433 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676729561/5000000000 : ℝ), (-2255882051/10000000000 : ℝ), (5233383331/10000000000 : ℝ)] ![(43695142862127/100000000000000 : ℝ), (434486489263/3125000000000 : ℝ), (21200644733433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676729561/5000000000 : ℝ)|^8349 ≤ (43695142862127/100000000000000 : ℝ)^6301
        have hw : |(2676729561/5000000000 : ℝ)|=(2676729561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255882051/10000000000 : ℝ)|^8349 ≤ (434486489263/3125000000000 : ℝ)^6301
        have hw : |(-2255882051/10000000000 : ℝ)|=(2255882051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233383331/10000000000 : ℝ)|^8349 ≤ (21200644733433/50000000000000 : ℝ)^6301
        have hw : |(5233383331/10000000000 : ℝ)|=(5233383331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676729601/5000000000 : ℝ)*x 0 + (5233383373/10000000000 : ℝ)*x 1 + (-225588189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676729601/5000000000 : ℝ)^8349 ≤ (21847571863661/50000000000000 : ℝ)^6301 := by
    have hnat : (2676729601 : ℕ)^8349*50000000000000^6301 ≤ 21847571863661^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676729601 5000000000 21847571863661 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233383373/10000000000 : ℝ)^8349 ≤ (10600322479439/25000000000000 : ℝ)^6301 := by
    have hnat : (5233383373 : ℕ)^8349*25000000000000^6301 ≤ 10600322479439^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233383373 10000000000 10600322479439 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225588189/1000000000 : ℝ)^8349 ≤ (13903566341613/100000000000000 : ℝ)^6301 := by
    have hnat : (225588189 : ℕ)^8349*100000000000000^6301 ≤ 13903566341613^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225588189 1000000000 13903566341613 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676729601/5000000000 : ℝ), (5233383373/10000000000 : ℝ), (-225588189/1000000000 : ℝ)] ![(21847571863661/50000000000000 : ℝ), (10600322479439/25000000000000 : ℝ), (13903566341613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676729601/5000000000 : ℝ)|^8349 ≤ (21847571863661/50000000000000 : ℝ)^6301
        have hw : |(2676729601/5000000000 : ℝ)|=(2676729601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233383373/10000000000 : ℝ)|^8349 ≤ (10600322479439/25000000000000 : ℝ)^6301
        have hw : |(5233383373/10000000000 : ℝ)|=(5233383373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225588189/1000000000 : ℝ)|^8349 ≤ (13903566341613/100000000000000 : ℝ)^6301
        have hw : |(-225588189/1000000000 : ℝ)|=(225588189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360535027/10000000000 : ℝ)*x 0 + (4170929359/10000000000 : ℝ)*x 1 + (4558678841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360535027/10000000000 : ℝ)^8349 ≤ (33295090256967/100000000000000 : ℝ)^6301 := by
    have hnat : (4360535027 : ℕ)^8349*100000000000000^6301 ≤ 33295090256967^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360535027 10000000000 33295090256967 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170929359/10000000000 : ℝ)^8349 ≤ (15695240057947/50000000000000 : ℝ)^6301 := by
    have hnat : (4170929359 : ℕ)^8349*50000000000000^6301 ≤ 15695240057947^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170929359 10000000000 15695240057947 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4558678841/10000000000 : ℝ)^8349 ≤ (17657214809401/50000000000000 : ℝ)^6301 := by
    have hnat : (4558678841 : ℕ)^8349*50000000000000^6301 ≤ 17657214809401^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558678841 10000000000 17657214809401 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360535027/10000000000 : ℝ), (4170929359/10000000000 : ℝ), (4558678841/10000000000 : ℝ)] ![(33295090256967/100000000000000 : ℝ), (15695240057947/50000000000000 : ℝ), (17657214809401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360535027/10000000000 : ℝ)|^8349 ≤ (33295090256967/100000000000000 : ℝ)^6301
        have hw : |(4360535027/10000000000 : ℝ)|=(4360535027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170929359/10000000000 : ℝ)|^8349 ≤ (15695240057947/50000000000000 : ℝ)^6301
        have hw : |(4170929359/10000000000 : ℝ)|=(4170929359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4558678841/10000000000 : ℝ)|^8349 ≤ (17657214809401/50000000000000 : ℝ)^6301
        have hw : |(4558678841/10000000000 : ℝ)|=(4558678841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215657599/1000000000 : ℝ)*x 0 + (2617065257/5000000000 : ℝ)*x 1 + (5426999037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215657599/1000000000 : ℝ)^8349 ≤ (13098447115741/100000000000000 : ℝ)^6301 := by
    have hnat : (215657599 : ℕ)^8349*100000000000000^6301 ≤ 13098447115741^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215657599 1000000000 13098447115741 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617065257/5000000000 : ℝ)^8349 ≤ (2650581938857/6250000000000 : ℝ)^6301 := by
    have hnat : (2617065257 : ℕ)^8349*6250000000000^6301 ≤ 2650581938857^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617065257 5000000000 2650581938857 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426999037/10000000000 : ℝ)^8349 ≤ (44492241852873/100000000000000 : ℝ)^6301 := by
    have hnat : (5426999037 : ℕ)^8349*100000000000000^6301 ≤ 44492241852873^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426999037 10000000000 44492241852873 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215657599/1000000000 : ℝ), (2617065257/5000000000 : ℝ), (5426999037/10000000000 : ℝ)] ![(13098447115741/100000000000000 : ℝ), (2650581938857/6250000000000 : ℝ), (44492241852873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215657599/1000000000 : ℝ)|^8349 ≤ (13098447115741/100000000000000 : ℝ)^6301
        have hw : |(-215657599/1000000000 : ℝ)|=(215657599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617065257/5000000000 : ℝ)|^8349 ≤ (2650581938857/6250000000000 : ℝ)^6301
        have hw : |(2617065257/5000000000 : ℝ)|=(2617065257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426999037/10000000000 : ℝ)|^8349 ≤ (44492241852873/100000000000000 : ℝ)^6301
        have hw : |(5426999037/10000000000 : ℝ)|=(5426999037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530416713/1000000000 : ℝ)*x 0 + (-1031133153/5000000000 : ℝ)*x 1 + (5426999081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530416713/1000000000 : ℝ)^8349 ≤ (43162852836629/100000000000000 : ℝ)^6301 := by
    have hnat : (530416713 : ℕ)^8349*100000000000000^6301 ≤ 43162852836629^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530416713 1000000000 43162852836629 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031133153/5000000000 : ℝ)^8349 ≤ (6172452408507/50000000000000 : ℝ)^6301 := by
    have hnat : (1031133153 : ℕ)^8349*50000000000000^6301 ≤ 6172452408507^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031133153 5000000000 6172452408507 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426999081/10000000000 : ℝ)^8349 ≤ (11123060582711/25000000000000 : ℝ)^6301 := by
    have hnat : (5426999081 : ℕ)^8349*25000000000000^6301 ≤ 11123060582711^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426999081 10000000000 11123060582711 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530416713/1000000000 : ℝ), (-1031133153/5000000000 : ℝ), (5426999081/10000000000 : ℝ)] ![(43162852836629/100000000000000 : ℝ), (6172452408507/50000000000000 : ℝ), (11123060582711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530416713/1000000000 : ℝ)|^8349 ≤ (43162852836629/100000000000000 : ℝ)^6301
        have hw : |(530416713/1000000000 : ℝ)|=(530416713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031133153/5000000000 : ℝ)|^8349 ≤ (6172452408507/50000000000000 : ℝ)^6301
        have hw : |(-1031133153/5000000000 : ℝ)|=(1031133153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426999081/10000000000 : ℝ)|^8349 ≤ (11123060582711/25000000000000 : ℝ)^6301
        have hw : |(5426999081/10000000000 : ℝ)|=(5426999081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652083503/5000000000 : ℝ)*x 0 + (2713499647/5000000000 : ℝ)*x 1 + (-257783273/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652083503/5000000000 : ℝ)^8349 ≤ (10790712874901/25000000000000 : ℝ)^6301 := by
    have hnat : (2652083503 : ℕ)^8349*25000000000000^6301 ≤ 10790712874901^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652083503 5000000000 10790712874901 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713499647/5000000000 : ℝ)^8349 ≤ (22246122322331/50000000000000 : ℝ)^6301 := by
    have hnat : (2713499647 : ℕ)^8349*50000000000000^6301 ≤ 22246122322331^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713499647 5000000000 22246122322331 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257783273/1250000000 : ℝ)^8349 ≤ (12344903849343/100000000000000 : ℝ)^6301 := by
    have hnat : (257783273 : ℕ)^8349*100000000000000^6301 ≤ 12344903849343^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257783273 1250000000 12344903849343 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652083503/5000000000 : ℝ), (2713499647/5000000000 : ℝ), (-257783273/1250000000 : ℝ)] ![(10790712874901/25000000000000 : ℝ), (22246122322331/50000000000000 : ℝ), (12344903849343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652083503/5000000000 : ℝ)|^8349 ≤ (10790712874901/25000000000000 : ℝ)^6301
        have hw : |(2652083503/5000000000 : ℝ)|=(2652083503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713499647/5000000000 : ℝ)|^8349 ≤ (22246122322331/50000000000000 : ℝ)^6301
        have hw : |(2713499647/5000000000 : ℝ)|=(2713499647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257783273/1250000000 : ℝ)|^8349 ≤ (12344903849343/100000000000000 : ℝ)^6301
        have hw : |(-257783273/1250000000 : ℝ)|=(257783273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s3_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180284899/5000000000 : ℝ)*x 0 + (4557188699/10000000000 : ℝ)*x 1 + (521553467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180284899/5000000000 : ℝ)^8349 ≤ (6659088409337/20000000000000 : ℝ)^6301 := by
    have hnat : (2180284899 : ℕ)^8349*20000000000000^6301 ≤ 6659088409337^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180284899 5000000000 6659088409337 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557188699/10000000000 : ℝ)^8349 ≤ (17649567427707/50000000000000 : ℝ)^6301 := by
    have hnat : (4557188699 : ℕ)^8349*50000000000000^6301 ≤ 17649567427707^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557188699 10000000000 17649567427707 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521553467/1250000000 : ℝ)^8349 ≤ (31405423073193/100000000000000 : ℝ)^6301 := by
    have hnat : (521553467 : ℕ)^8349*100000000000000^6301 ≤ 31405423073193^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521553467 1250000000 31405423073193 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180284899/5000000000 : ℝ), (4557188699/10000000000 : ℝ), (521553467/1250000000 : ℝ)] ![(6659088409337/20000000000000 : ℝ), (17649567427707/50000000000000 : ℝ), (31405423073193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180284899/5000000000 : ℝ)|^8349 ≤ (6659088409337/20000000000000 : ℝ)^6301
        have hw : |(2180284899/5000000000 : ℝ)|=(2180284899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557188699/10000000000 : ℝ)|^8349 ≤ (17649567427707/50000000000000 : ℝ)^6301
        have hw : |(4557188699/10000000000 : ℝ)|=(4557188699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521553467/1250000000 : ℝ)|^8349 ≤ (31405423073193/100000000000000 : ℝ)^6301
        have hw : |(521553467/1250000000 : ℝ)|=(521553467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2669/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14789/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16461/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16461/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16461/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16461/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16461/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16461/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9133/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (724756004014813/12500000000000000000 : ℝ) := by
    have hpowers : (9133/100000 : ℝ)^2087 ≤ (724756004014813/12500000000000000000 : ℝ)^512 := by
      have hnat : (9133 : ℕ)^2087*12500000000000000000^512 ≤ 724756004014813^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9133 100000 724756004014813 12500000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9133/100000 : ℝ)) (X := (724756004014813/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16461/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (63994236270071987/100000000000000000000 : ℝ) := by
    have hpowers : (16461/100000 : ℝ)^2087 ≤ (63994236270071987/100000000000000000000 : ℝ)^512 := by
      have hnat : (16461 : ℕ)^2087*100000000000000000000^512 ≤ 63994236270071987^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16461 100000 63994236270071987 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16461/100000 : ℝ)) (X := (63994236270071987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250724756004014813/6250000000000000000 : ℝ) ≤ (5000142236258097/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (6250724756004014813/6250000000000000000 : ℝ)^512 ≤ (5000142236258097/5000000000000000 : ℝ)^2087 := by
      have hnat : (6250724756004014813 : ℕ)^512*5000000000000000^2087 ≤ 5000142236258097^2087*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250724756004014813 6250000000000000000 5000142236258097 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000142236258097/5000000000000000 : ℝ)) (X := (6250724756004014813/6250000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100069792284302190491/100000000000000000000 : ℝ) ≤ (5000855875488691/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100069792284302190491/100000000000000000000 : ℝ)^512 ≤ (5000855875488691/5000000000000000 : ℝ)^2087 := by
      have hnat : (100069792284302190491 : ℕ)^512*5000000000000000^2087 ≤ 5000855875488691^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100069792284302190491 100000000000000000000 5000855875488691 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000855875488691/5000000000000000 : ℝ)) (X := (100069792284302190491/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063994236270071987/50000000000000000000 : ℝ) ≤ (1000313902943857/1000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50063994236270071987/50000000000000000000 : ℝ)^512 ≤ (1000313902943857/1000000000000000 : ℝ)^2087 := by
      have hnat : (50063994236270071987 : ℕ)^512*1000000000000000^2087 ≤ 1000313902943857^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063994236270071987 50000000000000000000 1000313902943857 1000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000313902943857/1000000000000000 : ℝ)) (X := (50063994236270071987/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(724756004014813/12500000000000000000 : ℝ) ≤ ((9157001743278326203/9160000000000000000 : ℝ)+2*(356819615297/183200000000000 : ℝ)*(9133/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (9157001743278326203/9160000000000000000 : ℝ)+2*(356819615297/183200000000000 : ℝ)*(9133/100000 : ℝ)=(5000142236258097/5000000000000000 : ℝ) by norm_num, show 1+2*(724756004014813/12500000000000000000 : ℝ)=(6250724756004014813/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63994236270071987/100000000000000000000 : ℝ)+(724756004014813/12500000000000000000 : ℝ) ≤ ((9157001743278326203/9160000000000000000 : ℝ)+(356819615297/183200000000000 : ℝ)*((16461/100000 : ℝ)+(9133/100000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (9157001743278326203/9160000000000000000 : ℝ)+(356819615297/183200000000000 : ℝ)*((16461/100000 : ℝ)+(9133/100000 : ℝ))=(5000855875488691/5000000000000000 : ℝ) by norm_num, show 1+(63994236270071987/100000000000000000000 : ℝ)+(724756004014813/12500000000000000000 : ℝ)=(100069792284302190491/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63994236270071987/100000000000000000000 : ℝ) ≤ ((9157001743278326203/9160000000000000000 : ℝ)+2*(356819615297/183200000000000 : ℝ)*(16461/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (9157001743278326203/9160000000000000000 : ℝ)+2*(356819615297/183200000000000 : ℝ)*(16461/100000 : ℝ)=(1000313902943857/1000000000000000 : ℝ) by norm_num, show 1+2*(63994236270071987/100000000000000000000 : ℝ)=(50063994236270071987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9157001743278326203/9160000000000000000 : ℝ)*(X 1 0+X 2 0)+(356819615297/183200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (9133/100000 : ℝ)) (hi := (16461/100000 : ℝ)) (c := (9157001743278326203/9160000000000000000 : ℝ)) (alpha := (356819615297/183200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9157001743278326203/9160000000000000000 : ℝ)*(X 0 1+X 2 1)+(356819615297/183200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (9133/100000 : ℝ)) (hi := (16461/100000 : ℝ)) (c := (9157001743278326203/9160000000000000000 : ℝ)) (alpha := (356819615297/183200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9157001743278326203/9160000000000000000 : ℝ)*(X 0 2+X 1 2)+(356819615297/183200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (9133/100000 : ℝ)) (hi := (16461/100000 : ℝ)) (c := (9157001743278326203/9160000000000000000 : ℝ)) (alpha := (356819615297/183200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-269569821/1250000000 : ℝ)*X 0 0+(1356937543/2500000000 : ℝ)*X 0 1+(2616691759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676729561/5000000000 : ℝ)*X 1 0+(-2255882051/10000000000 : ℝ)*X 1 1+(5233383331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676729601/5000000000 : ℝ)*X 2 0+(5233383373/10000000000 : ℝ)*X 2 1+(-225588189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360535027/10000000000 : ℝ)*X 0 0+(4170929359/10000000000 : ℝ)*X 0 1+(4558678841/10000000000 : ℝ)*X 0 2+(4360535027/10000000000 : ℝ)*X 1 0+(4170929359/10000000000 : ℝ)*X 1 1+(4558678841/10000000000 : ℝ)*X 1 2+(4360535027/10000000000 : ℝ)*X 2 0+(4170929359/10000000000 : ℝ)*X 2 1+(4558678841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215657599/1000000000 : ℝ)*X 0 0+(2617065257/5000000000 : ℝ)*X 0 1+(5426999037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530416713/1000000000 : ℝ)*X 1 0+(-1031133153/5000000000 : ℝ)*X 1 1+(5426999081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652083503/5000000000 : ℝ)*X 2 0+(2713499647/5000000000 : ℝ)*X 2 1+(-257783273/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180284899/5000000000 : ℝ)*X 0 0+(4557188699/10000000000 : ℝ)*X 0 1+(521553467/1250000000 : ℝ)*X 0 2+(2180284899/5000000000 : ℝ)*X 1 0+(4557188699/10000000000 : ℝ)*X 1 1+(521553467/1250000000 : ℝ)*X 1 2+(2180284899/5000000000 : ℝ)*X 2 0+(4557188699/10000000000 : ℝ)*X 2 1+(521553467/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (378494334412297051671707919/57250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25665607/1562500000000 : ℝ)*(base19) + (1569874823/100000000000000 : ℝ)*(base23) + (40046127/50000000000000 : ℝ)*(lower2) + (11434399/10000000000000 : ℝ)*(upper3) + (93494699/50000000000000 : ℝ)*(upper5) + (965497713274409/25000000000000 : ℝ)*(major0) + (965497713274409/25000000000000 : ℝ)*(major1) + (965497713274409/25000000000000 : ℝ)*(major2) + (2572470185632943/50000000000000 : ℝ)*(sp0) + (5144968292876551/100000000000000 : ℝ)*(sp1) + (80390130712509/1562500000000 : ℝ)*(sp2) + (2578998177648907/100000000000000 : ℝ)*(sp3) + (14782104757/50000000000000 : ℝ)*(sp4) + (3343173949/25000000000000 : ℝ)*(sp7) + (1289505775172351/50000000000000 : ℝ)*(f.failure) + (5144969935475399/100000000000000 : ℝ)*(f.sum) + (13486604974337/2290000000000000000000000000 : ℝ)*base66 + (2367863101132689027/229000000000000000000000000000000 : ℝ)*base67 + (483956357216689027/229000000000000000000000000000000 : ℝ)*base69 + (1752936199226689027/229000000000000000000000000000000 : ℝ)*base71 + (1954110866833/2290000000000000000000000000 : ℝ)*base73 + (1099538948181689027/229000000000000000000000000000000 : ℝ)*base75 + (3805546938543310973/229000000000000000000000000000000 : ℝ)*base78 + (3859367521592689027/229000000000000000000000000000000 : ℝ)*base79 + (3145318287603/2290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (40316411/5000000000000000000000 : ℝ)*base90 + (40316411/5000000000000000000000 : ℝ)*base92 + (40316411/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20221913058884565571611/4580000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468769881/50000000000000 : ℝ)*(base19) + (997655023/100000000000000 : ℝ)*(base23) + (2282889/2000000000000 : ℝ)*(upper3) + (17127161/25000000000000 : ℝ)*(lower4) + (1021217/1000000000000 : ℝ)*(upper5) + (1945973239764067/50000000000000 : ℝ)*(major0) + (1945973239764067/50000000000000 : ℝ)*(major1) + (1945973239764067/50000000000000 : ℝ)*(major2) + (17426579571/100000000000000 : ℝ)*(sp1) + (23039963879/100000000000000 : ℝ)*(sp2) + (5184877095420523/100000000000000 : ℝ)*(sp4) + (518485873130119/10000000000000 : ℝ)*(sp5) + (259242652890081/5000000000000 : ℝ)*(sp6) + (649753929115061/25000000000000 : ℝ)*(sp7) + (649753929115061/25000000000000 : ℝ)*(f.failure) + (5184877095420523/100000000000000 : ℝ)*(f.sum) + (2973747041461/4580000000000000000000000000 : ℝ)*base66 + (316119262095102399/458000000000000000000000000000000 : ℝ)*base68 + (885157953201102399/458000000000000000000000000000000 : ℝ)*base70 + (2880688359136897601/458000000000000000000000000000000 : ℝ)*base71 + (18653974058201/4580000000000000000000000000 : ℝ)*base74 + (6312321029521102399/458000000000000000000000000000000 : ℝ)*base76 + (2092546883608897601/458000000000000000000000000000000 : ℝ)*base77 + (3020364331054897601/458000000000000000000000000000000 : ℝ)*base79 + (12184998395621/4580000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13548279/2500000000000000000000 : ℝ)*base89 + (13548279/2500000000000000000000 : ℝ)*base91 + (13548279/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1156_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_s4_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079725133/5000000000 : ℝ)*x 0 + (270061373/500000000 : ℝ)*x 1 + (2629007041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079725133/5000000000 : ℝ)^8349 ≤ (13121583874811/100000000000000 : ℝ)^6301 := by
    have hnat : (1079725133 : ℕ)^8349*100000000000000^6301 ≤ 13121583874811^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079725133 5000000000 13121583874811 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270061373/500000000 : ℝ)^8349 ≤ (5526562707559/12500000000000 : ℝ)^6301 := by
    have hnat : (270061373 : ℕ)^8349*12500000000000^6301 ≤ 5526562707559^6301*500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270061373 500000000 5526562707559 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629007041/5000000000 : ℝ)^8349 ≤ (42665914455343/100000000000000 : ℝ)^6301 := by
    have hnat : (2629007041 : ℕ)^8349*100000000000000^6301 ≤ 42665914455343^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629007041 5000000000 42665914455343 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079725133/5000000000 : ℝ), (270061373/500000000 : ℝ), (2629007041/5000000000 : ℝ)] ![(13121583874811/100000000000000 : ℝ), (5526562707559/12500000000000 : ℝ), (42665914455343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079725133/5000000000 : ℝ)|^8349 ≤ (13121583874811/100000000000000 : ℝ)^6301
        have hw : |(-1079725133/5000000000 : ℝ)|=(1079725133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270061373/500000000 : ℝ)|^8349 ≤ (5526562707559/12500000000000 : ℝ)^6301
        have hw : |(270061373/500000000 : ℝ)|=(270061373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629007041/5000000000 : ℝ)|^8349 ≤ (42665914455343/100000000000000 : ℝ)^6301
        have hw : |(2629007041/5000000000 : ℝ)|=(2629007041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673412899/5000000000 : ℝ)*x 0 + (-1116109961/5000000000 : ℝ)*x 1 + (2629007301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673412899/5000000000 : ℝ)^8349 ≤ (1090585459673/2500000000000 : ℝ)^6301 := by
    have hnat : (2673412899 : ℕ)^8349*2500000000000^6301 ≤ 1090585459673^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673412899 5000000000 1090585459673 2500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116109961/5000000000 : ℝ)^8349 ≤ (109685292427/800000000000 : ℝ)^6301 := by
    have hnat : (1116109961 : ℕ)^8349*800000000000^6301 ≤ 109685292427^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116109961 5000000000 109685292427 800000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629007301/5000000000 : ℝ)^8349 ≤ (42665920046319/100000000000000 : ℝ)^6301 := by
    have hnat : (2629007301 : ℕ)^8349*100000000000000^6301 ≤ 42665920046319^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629007301 5000000000 42665920046319 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673412899/5000000000 : ℝ), (-1116109961/5000000000 : ℝ), (2629007301/5000000000 : ℝ)] ![(1090585459673/2500000000000 : ℝ), (109685292427/800000000000 : ℝ), (42665920046319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673412899/5000000000 : ℝ)|^8349 ≤ (1090585459673/2500000000000 : ℝ)^6301
        have hw : |(2673412899/5000000000 : ℝ)|=(2673412899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116109961/5000000000 : ℝ)|^8349 ≤ (109685292427/800000000000 : ℝ)^6301
        have hw : |(-1116109961/5000000000 : ℝ)|=(1116109961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629007301/5000000000 : ℝ)|^8349 ≤ (42665920046319/100000000000000 : ℝ)^6301
        have hw : |(2629007301/5000000000 : ℝ)|=(2629007301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673413429/5000000000 : ℝ)*x 0 + (1314503293/2500000000 : ℝ)*x 1 + (-2232220403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673413429/5000000000 : ℝ)^8349 ≤ (21811714923063/50000000000000 : ℝ)^6301 := by
    have hnat : (2673413429 : ℕ)^8349*50000000000000^6301 ≤ 21811714923063^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673413429 5000000000 21811714923063 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314503293/2500000000 : ℝ)^8349 ≤ (8533180934227/20000000000000 : ℝ)^6301 := by
    have hnat : (1314503293 : ℕ)^8349*20000000000000^6301 ≤ 8533180934227^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314503293 2500000000 8533180934227 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2232220403/10000000000 : ℝ)^8349 ≤ (3427666367003/25000000000000 : ℝ)^6301 := by
    have hnat : (2232220403 : ℕ)^8349*25000000000000^6301 ≤ 3427666367003^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232220403 10000000000 3427666367003 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673413429/5000000000 : ℝ), (1314503293/2500000000 : ℝ), (-2232220403/10000000000 : ℝ)] ![(21811714923063/50000000000000 : ℝ), (8533180934227/20000000000000 : ℝ), (3427666367003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673413429/5000000000 : ℝ)|^8349 ≤ (21811714923063/50000000000000 : ℝ)^6301
        have hw : |(2673413429/5000000000 : ℝ)|=(2673413429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314503293/2500000000 : ℝ)|^8349 ≤ (8533180934227/20000000000000 : ℝ)^6301
        have hw : |(1314503293/2500000000 : ℝ)|=(1314503293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2232220403/10000000000 : ℝ)|^8349 ≤ (3427666367003/25000000000000 : ℝ)^6301
        have hw : |(-2232220403/10000000000 : ℝ)|=(2232220403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436226143/1000000000 : ℝ)*x 0 + (1055432391/2500000000 : ℝ)*x 1 + (4507432367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436226143/1000000000 : ℝ)^8349 ≤ (832813948719/2500000000000 : ℝ)^6301 := by
    have hnat : (436226143 : ℕ)^8349*2500000000000^6301 ≤ 832813948719^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436226143 1000000000 832813948719 2500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055432391/2500000000 : ℝ)^8349 ≤ (31898068883651/100000000000000 : ℝ)^6301 := by
    have hnat : (1055432391 : ℕ)^8349*100000000000000^6301 ≤ 31898068883651^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055432391 2500000000 31898068883651 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507432367/10000000000 : ℝ)^8349 ≤ (17394686576979/50000000000000 : ℝ)^6301 := by
    have hnat : (4507432367 : ℕ)^8349*50000000000000^6301 ≤ 17394686576979^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507432367 10000000000 17394686576979 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436226143/1000000000 : ℝ), (1055432391/2500000000 : ℝ), (4507432367/10000000000 : ℝ)] ![(832813948719/2500000000000 : ℝ), (31898068883651/100000000000000 : ℝ), (17394686576979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436226143/1000000000 : ℝ)|^8349 ≤ (832813948719/2500000000000 : ℝ)^6301
        have hw : |(436226143/1000000000 : ℝ)|=(436226143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055432391/2500000000 : ℝ)|^8349 ≤ (31898068883651/100000000000000 : ℝ)^6301
        have hw : |(1055432391/2500000000 : ℝ)|=(1055432391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507432367/10000000000 : ℝ)|^8349 ≤ (17394686576979/50000000000000 : ℝ)^6301
        have hw : |(4507432367/10000000000 : ℝ)|=(4507432367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079728741/5000000000 : ℝ)*x 0 + (5258419933/10000000000 : ℝ)*x 1 + (5400819771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079728741/5000000000 : ℝ)^8349 ≤ (2624328394659/20000000000000 : ℝ)^6301 := by
    have hnat : (1079728741 : ℕ)^8349*20000000000000^6301 ≤ 2624328394659^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079728741 5000000000 2624328394659 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258419933/10000000000 : ℝ)^8349 ≤ (8534055634037/20000000000000 : ℝ)^6301 := by
    have hnat : (5258419933 : ℕ)^8349*20000000000000^6301 ≤ 8534055634037^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258419933 10000000000 8534055634037 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400819771/10000000000 : ℝ)^8349 ≤ (11052019959583/25000000000000 : ℝ)^6301 := by
    have hnat : (5400819771 : ℕ)^8349*25000000000000^6301 ≤ 11052019959583^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400819771 10000000000 11052019959583 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079728741/5000000000 : ℝ), (5258419933/10000000000 : ℝ), (5400819771/10000000000 : ℝ)] ![(2624328394659/20000000000000 : ℝ), (8534055634037/20000000000000 : ℝ), (11052019959583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079728741/5000000000 : ℝ)|^8349 ≤ (2624328394659/20000000000000 : ℝ)^6301
        have hw : |(-1079728741/5000000000 : ℝ)|=(1079728741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258419933/10000000000 : ℝ)|^8349 ≤ (8534055634037/20000000000000 : ℝ)^6301
        have hw : |(5258419933/10000000000 : ℝ)|=(5258419933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400819771/10000000000 : ℝ)|^8349 ≤ (11052019959583/25000000000000 : ℝ)^6301
        have hw : |(5400819771/10000000000 : ℝ)|=(5400819771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310507581/10000000000 : ℝ)*x 0 + (-2089413613/10000000000 : ℝ)*x 1 + (540081969/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310507581/10000000000 : ℝ)^8349 ≤ (43231231783979/100000000000000 : ℝ)^6301 := by
    have hnat : (5310507581 : ℕ)^8349*100000000000000^6301 ≤ 43231231783979^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310507581 10000000000 43231231783979 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089413613/10000000000 : ℝ)^8349 ≤ (3140172311147/25000000000000 : ℝ)^6301 := by
    have hnat : (2089413613 : ℕ)^8349*25000000000000^6301 ≤ 3140172311147^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089413613 10000000000 3140172311147 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540081969/1000000000 : ℝ)^8349 ≤ (44208078959811/100000000000000 : ℝ)^6301 := by
    have hnat : (540081969 : ℕ)^8349*100000000000000^6301 ≤ 44208078959811^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540081969 1000000000 44208078959811 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310507581/10000000000 : ℝ), (-2089413613/10000000000 : ℝ), (540081969/1000000000 : ℝ)] ![(43231231783979/100000000000000 : ℝ), (3140172311147/25000000000000 : ℝ), (44208078959811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310507581/10000000000 : ℝ)|^8349 ≤ (43231231783979/100000000000000 : ℝ)^6301
        have hw : |(5310507581/10000000000 : ℝ)|=(5310507581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089413613/10000000000 : ℝ)|^8349 ≤ (3140172311147/25000000000000 : ℝ)^6301
        have hw : |(-2089413613/10000000000 : ℝ)|=(2089413613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540081969/1000000000 : ℝ)|^8349 ≤ (44208078959811/100000000000000 : ℝ)^6301
        have hw : |(540081969/1000000000 : ℝ)|=(540081969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165953357/312500000 : ℝ)*x 0 + (1350204927/2500000000 : ℝ)*x 1 + (-2089413801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165953357/312500000 : ℝ)^8349 ≤ (1729249203619/4000000000000 : ℝ)^6301 := by
    have hnat : (165953357 : ℕ)^8349*4000000000000^6301 ≤ 1729249203619^6301*312500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165953357 312500000 1729249203619 4000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350204927/2500000000 : ℝ)^8349 ≤ (22104039577519/50000000000000 : ℝ)^6301 := by
    have hnat : (1350204927 : ℕ)^8349*50000000000000^6301 ≤ 22104039577519^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350204927 2500000000 22104039577519 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089413801/10000000000 : ℝ)^8349 ≤ (2512138148421/20000000000000 : ℝ)^6301 := by
    have hnat : (2089413801 : ℕ)^8349*20000000000000^6301 ≤ 2512138148421^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089413801 10000000000 2512138148421 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165953357/312500000 : ℝ), (1350204927/2500000000 : ℝ), (-2089413801/10000000000 : ℝ)] ![(1729249203619/4000000000000 : ℝ), (22104039577519/50000000000000 : ℝ), (2512138148421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165953357/312500000 : ℝ)|^8349 ≤ (1729249203619/4000000000000 : ℝ)^6301
        have hw : |(165953357/312500000 : ℝ)|=(165953357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350204927/2500000000 : ℝ)|^8349 ≤ (22104039577519/50000000000000 : ℝ)^6301
        have hw : |(1350204927/2500000000 : ℝ)|=(1350204927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089413801/10000000000 : ℝ)|^8349 ≤ (2512138148421/20000000000000 : ℝ)^6301
        have hw : |(-2089413801/10000000000 : ℝ)|=(2089413801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s4_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436227553/1000000000 : ℝ)*x 0 + (4506621747/10000000000 : ℝ)*x 1 + (4222543321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436227553/1000000000 : ℝ)^8349 ≤ (33312700621373/100000000000000 : ℝ)^6301 := by
    have hnat : (436227553 : ℕ)^8349*100000000000000^6301 ≤ 33312700621373^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436227553 1000000000 33312700621373 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506621747/10000000000 : ℝ)^8349 ≤ (695621665959/2000000000000 : ℝ)^6301 := by
    have hnat : (4506621747 : ℕ)^8349*2000000000000^6301 ≤ 695621665959^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506621747 10000000000 695621665959 2000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222543321/10000000000 : ℝ)^8349 ≤ (15953108031757/50000000000000 : ℝ)^6301 := by
    have hnat : (4222543321 : ℕ)^8349*50000000000000^6301 ≤ 15953108031757^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222543321 10000000000 15953108031757 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436227553/1000000000 : ℝ), (4506621747/10000000000 : ℝ), (4222543321/10000000000 : ℝ)] ![(33312700621373/100000000000000 : ℝ), (695621665959/2000000000000 : ℝ), (15953108031757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436227553/1000000000 : ℝ)|^8349 ≤ (33312700621373/100000000000000 : ℝ)^6301
        have hw : |(436227553/1000000000 : ℝ)|=(436227553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506621747/10000000000 : ℝ)|^8349 ≤ (695621665959/2000000000000 : ℝ)^6301
        have hw : |(4506621747/10000000000 : ℝ)|=(4506621747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222543321/10000000000 : ℝ)|^8349 ≤ (15953108031757/50000000000000 : ℝ)^6301
        have hw : |(4222543321/10000000000 : ℝ)|=(4222543321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2669/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2669/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2669/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2669/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2669/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2669/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2669/25000 : ℝ) ^ (2087/512 : ℝ) ≤ (10955351569907873/100000000000000000000 : ℝ) := by
    have hpowers : (2669/25000 : ℝ)^2087 ≤ (10955351569907873/100000000000000000000 : ℝ)^512 := by
      have hnat : (2669 : ℕ)^2087*100000000000000000000^512 ≤ 10955351569907873^512*25000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2669 25000 10955351569907873 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2669/25000 : ℝ)) (X := (10955351569907873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14789/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (827099796827879/2000000000000000000 : ℝ) := by
    have hpowers : (14789/100000 : ℝ)^2087 ≤ (827099796827879/2000000000000000000 : ℝ)^512 := by
      have hnat : (14789 : ℕ)^2087*2000000000000000000^512 ≤ 827099796827879^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14789 100000 827099796827879 2000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14789/100000 : ℝ)) (X := (827099796827879/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010955351569907873/50000000000000000000 : ℝ) ≤ (1250067185868671/1250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50010955351569907873/50000000000000000000 : ℝ)^512 ≤ (1250067185868671/1250000000000000 : ℝ)^2087 := by
      have hnat : (50010955351569907873 : ℕ)^512*1250000000000000^2087 ≤ 1250067185868671^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010955351569907873 50000000000000000000 1250067185868671 1250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250067185868671/1250000000000000 : ℝ)) (X := (50010955351569907873/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052310341411301823/100000000000000000000 : ℝ) ≤ (1250160383384399/1250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100052310341411301823/100000000000000000000 : ℝ)^512 ≤ (1250160383384399/1250000000000000 : ℝ)^2087 := by
      have hnat : (100052310341411301823 : ℕ)^512*1250000000000000^2087 ≤ 1250160383384399^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052310341411301823 100000000000000000000 1250160383384399 1250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250160383384399/1250000000000000 : ℝ)) (X := (100052310341411301823/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000827099796827879/1000000000000000000 : ℝ) ≤ (1250253580900127/1250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (1000827099796827879/1000000000000000000 : ℝ)^512 ≤ (1250253580900127/1250000000000000 : ℝ)^2087 := by
      have hnat : (1000827099796827879 : ℕ)^512*1250000000000000^2087 ≤ 1250253580900127^2087*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000827099796827879 1000000000000000000 1250253580900127 1250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250253580900127/1250000000000000 : ℝ)) (X := (1000827099796827879/1000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10955351569907873/100000000000000000000 : ℝ) ≤ ((1713178794040673189/1713750000000000000 : ℝ)+2*(1941614911/1071093750000 : ℝ)*(2669/25000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (1713178794040673189/1713750000000000000 : ℝ)+2*(1941614911/1071093750000 : ℝ)*(2669/25000 : ℝ)=(1250067185868671/1250000000000000 : ℝ) by norm_num, show 1+2*(10955351569907873/100000000000000000000 : ℝ)=(50010955351569907873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(827099796827879/2000000000000000000 : ℝ)+(10955351569907873/100000000000000000000 : ℝ) ≤ ((1713178794040673189/1713750000000000000 : ℝ)+(1941614911/1071093750000 : ℝ)*((14789/100000 : ℝ)+(2669/25000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (1713178794040673189/1713750000000000000 : ℝ)+(1941614911/1071093750000 : ℝ)*((14789/100000 : ℝ)+(2669/25000 : ℝ))=(1250160383384399/1250000000000000 : ℝ) by norm_num, show 1+(827099796827879/2000000000000000000 : ℝ)+(10955351569907873/100000000000000000000 : ℝ)=(100052310341411301823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(827099796827879/2000000000000000000 : ℝ) ≤ ((1713178794040673189/1713750000000000000 : ℝ)+2*(1941614911/1071093750000 : ℝ)*(14789/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (1713178794040673189/1713750000000000000 : ℝ)+2*(1941614911/1071093750000 : ℝ)*(14789/100000 : ℝ)=(1250253580900127/1250000000000000 : ℝ) by norm_num, show 1+2*(827099796827879/2000000000000000000 : ℝ)=(1000827099796827879/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1713178794040673189/1713750000000000000 : ℝ)*(X 1 0+X 2 0)+(1941614911/1071093750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (1713178794040673189/1713750000000000000 : ℝ)) (alpha := (1941614911/1071093750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1713178794040673189/1713750000000000000 : ℝ)*(X 0 1+X 2 1)+(1941614911/1071093750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (1713178794040673189/1713750000000000000 : ℝ)) (alpha := (1941614911/1071093750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1713178794040673189/1713750000000000000 : ℝ)*(X 0 2+X 1 2)+(1941614911/1071093750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (1713178794040673189/1713750000000000000 : ℝ)) (alpha := (1941614911/1071093750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079725133/5000000000 : ℝ)*X 0 0+(270061373/500000000 : ℝ)*X 0 1+(2629007041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673412899/5000000000 : ℝ)*X 1 0+(-1116109961/5000000000 : ℝ)*X 1 1+(2629007301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673413429/5000000000 : ℝ)*X 2 0+(1314503293/2500000000 : ℝ)*X 2 1+(-2232220403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436226143/1000000000 : ℝ)*X 0 0+(1055432391/2500000000 : ℝ)*X 0 1+(4507432367/10000000000 : ℝ)*X 0 2+(436226143/1000000000 : ℝ)*X 1 0+(1055432391/2500000000 : ℝ)*X 1 1+(4507432367/10000000000 : ℝ)*X 1 2+(436226143/1000000000 : ℝ)*X 2 0+(1055432391/2500000000 : ℝ)*X 2 1+(4507432367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079728741/5000000000 : ℝ)*X 0 0+(5258419933/10000000000 : ℝ)*X 0 1+(5400819771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310507581/10000000000 : ℝ)*X 1 0+(-2089413613/10000000000 : ℝ)*X 1 1+(540081969/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165953357/312500000 : ℝ)*X 2 0+(1350204927/2500000000 : ℝ)*X 2 1+(-2089413801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436227553/1000000000 : ℝ)*X 0 0+(4506621747/10000000000 : ℝ)*X 0 1+(4222543321/10000000000 : ℝ)*X 0 2+(436227553/1000000000 : ℝ)*X 1 0+(4506621747/10000000000 : ℝ)*X 1 1+(4222543321/10000000000 : ℝ)*X 1 2+(436227553/1000000000 : ℝ)*X 2 0+(4506621747/10000000000 : ℝ)*X 2 1+(4222543321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10667270180767380483044859/1785156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (236140131/100000000000000 : ℝ)*(base15) + (61699693/25000000000000 : ℝ)*(lower2) + (119672817/100000000000000 : ℝ)*(upper3) + (243781179/100000000000000 : ℝ)*(upper4) + (1310342891928813/25000000000000 : ℝ)*(major0) + (1310342891928813/25000000000000 : ℝ)*(major1) + (1310342891928813/25000000000000 : ℝ)*(major2) + (6982581858967723/100000000000000 : ℝ)*(sp0) + (1745647493492179/25000000000000 : ℝ)*(sp1) + (3491275873684299/50000000000000 : ℝ)*(sp2) + (140005670385593/4000000000000 : ℝ)*(sp3) + (2087785281/25000000000000 : ℝ)*(sp4) + (38462740249/100000000000000 : ℝ)*(sp6) + (10966497203/100000000000000 : ℝ)*(sp7) + (875038181534257/25000000000000 : ℝ)*(f.failure) + (6982590210108847/100000000000000 : ℝ)*(f.sum) + (15329709573659/1142500000000000000000000000 : ℝ)*base66 + (81559122842091969/14281250000000000000000000000000 : ℝ)*base67 + (273910042746623219/14281250000000000000000000000000 : ℝ)*base69 + (83416120991623219/14281250000000000000000000000000 : ℝ)*base71 + (3577966245207/2285000000000000000000000000 : ℝ)*base73 + (14447719312564281/14281250000000000000000000000000 : ℝ)*base76 + (209711237258998219/14281250000000000000000000000000 : ℝ)*base77 + (43738061675466969/14281250000000000000000000000000 : ℝ)*base79 + (6284855606997/2285000000000000000000000000 : ℝ)*base81 + (9389323/2500000000000000000000 : ℝ)*base89 + (9389323/2500000000000000000000 : ℝ)*base91 + (9389323/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32624596639174729973025999/3570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (105583309/4000000000000 : ℝ)*(base19) + (2489734133/100000000000000 : ℝ)*(base23) + (78470859/100000000000000 : ℝ)*(upper2) + (150984389/100000000000000 : ℝ)*(upper3) + (320795091/100000000000000 : ℝ)*(upper5) + (658914528031667/12500000000000 : ℝ)*(major0) + (658914528031667/12500000000000 : ℝ)*(major1) + (658914528031667/12500000000000 : ℝ)*(major2) + (70454435819/100000000000000 : ℝ)*(sp1) + (57292418057/100000000000000 : ℝ)*(sp2) + (3511241288641569/50000000000000 : ℝ)*(sp4) + (1404481896652919/20000000000000 : ℝ)*(sp5) + (7022422795130947/100000000000000 : ℝ)*(sp6) + (35201495666321/1000000000000 : ℝ)*(sp7) + (35201495666321/1000000000000 : ℝ)*(f.failure) + (3511241288641569/50000000000000 : ℝ)*(f.sum) + (1825940292883/1713750000000000000000000000 : ℝ)*base66 + (122476627040348271/7140625000000000000000000000000 : ℝ)*base67 + (133690571273035771/7140625000000000000000000000000 : ℝ)*base69 + (26516336072700349/1785156250000000000000000000000 : ℝ)*base71 + (5495318689897/6855000000000000000000000000 : ℝ)*base74 + (26906928806942021/7140625000000000000000000000000 : ℝ)*base75 + (126869039839410771/7140625000000000000000000000000 : ℝ)*base77 + (10274450465620479/7140625000000000000000000000000 : ℝ)*base80 + (1109405979161/3427500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (858581/100000000000000000000 : ℝ)*base90 + (858581/100000000000000000000 : ℝ)*base92 + (858581/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1156_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_s5_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135003353/625000000 : ℝ)*x 0 + (5394550231/10000000000 : ℝ)*x 1 + (5264295463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135003353/625000000 : ℝ)^8349 ≤ (6563221063781/50000000000000 : ℝ)^6301 := by
    have hnat : (135003353 : ℕ)^8349*50000000000000^6301 ≤ 6563221063781^6301*625000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135003353 625000000 6563221063781 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394550231/10000000000 : ℝ)^8349 ≤ (22070046827157/50000000000000 : ℝ)^6301 := by
    have hnat : (5394550231 : ℕ)^8349*50000000000000^6301 ≤ 22070046827157^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394550231 10000000000 22070046827157 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264295463/10000000000 : ℝ)^8349 ≤ (21366732100347/50000000000000 : ℝ)^6301 := by
    have hnat : (5264295463 : ℕ)^8349*50000000000000^6301 ≤ 21366732100347^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264295463 10000000000 21366732100347 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135003353/625000000 : ℝ), (5394550231/10000000000 : ℝ), (5264295463/10000000000 : ℝ)] ![(6563221063781/50000000000000 : ℝ), (22070046827157/50000000000000 : ℝ), (21366732100347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135003353/625000000 : ℝ)|^8349 ≤ (6563221063781/50000000000000 : ℝ)^6301
        have hw : |(-135003353/625000000 : ℝ)|=(135003353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394550231/10000000000 : ℝ)|^8349 ≤ (22070046827157/50000000000000 : ℝ)^6301
        have hw : |(5394550231/10000000000 : ℝ)|=(5394550231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264295463/10000000000 : ℝ)|^8349 ≤ (21366732100347/50000000000000 : ℝ)^6301
        have hw : |(5264295463/10000000000 : ℝ)|=(5264295463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672575303/5000000000 : ℝ)*x 0 + (-222614323/1000000000 : ℝ)*x 1 + (41127307/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672575303/5000000000 : ℝ)^8349 ≤ (43605309526699/100000000000000 : ℝ)^6301 := by
    have hnat : (2672575303 : ℕ)^8349*100000000000000^6301 ≤ 43605309526699^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672575303 5000000000 43605309526699 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222614323/1000000000 : ℝ)^8349 ≤ (853826753469/6250000000000 : ℝ)^6301 := by
    have hnat : (222614323 : ℕ)^8349*6250000000000^6301 ≤ 853826753469^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222614323 1000000000 853826753469 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41127307/78125000 : ℝ)^8349 ≤ (42733462404433/100000000000000 : ℝ)^6301 := by
    have hnat : (41127307 : ℕ)^8349*100000000000000^6301 ≤ 42733462404433^6301*78125000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41127307 78125000 42733462404433 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672575303/5000000000 : ℝ), (-222614323/1000000000 : ℝ), (41127307/78125000 : ℝ)] ![(43605309526699/100000000000000 : ℝ), (853826753469/6250000000000 : ℝ), (42733462404433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672575303/5000000000 : ℝ)|^8349 ≤ (43605309526699/100000000000000 : ℝ)^6301
        have hw : |(2672575303/5000000000 : ℝ)|=(2672575303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222614323/1000000000 : ℝ)|^8349 ≤ (853826753469/6250000000000 : ℝ)^6301
        have hw : |(-222614323/1000000000 : ℝ)|=(222614323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41127307/78125000 : ℝ)|^8349 ≤ (42733462404433/100000000000000 : ℝ)^6301
        have hw : |(41127307/78125000 : ℝ)|=(41127307/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213806023/400000000 : ℝ)*x 0 + (2632147677/5000000000 : ℝ)*x 1 + (-2226143193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213806023/400000000 : ℝ)^8349 ≤ (21802654595803/50000000000000 : ℝ)^6301 := by
    have hnat : (213806023 : ℕ)^8349*50000000000000^6301 ≤ 21802654595803^6301*400000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213806023 400000000 21802654595803 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632147677/5000000000 : ℝ)^8349 ≤ (10683365757071/25000000000000 : ℝ)^6301 := by
    have hnat : (2632147677 : ℕ)^8349*25000000000000^6301 ≤ 10683365757071^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632147677 5000000000 10683365757071 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226143193/10000000000 : ℝ)^8349 ≤ (2732245550929/20000000000000 : ℝ)^6301 := by
    have hnat : (2226143193 : ℕ)^8349*20000000000000^6301 ≤ 2732245550929^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226143193 10000000000 2732245550929 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213806023/400000000 : ℝ), (2632147677/5000000000 : ℝ), (-2226143193/10000000000 : ℝ)] ![(21802654595803/50000000000000 : ℝ), (10683365757071/25000000000000 : ℝ), (2732245550929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213806023/400000000 : ℝ)|^8349 ≤ (21802654595803/50000000000000 : ℝ)^6301
        have hw : |(213806023/400000000 : ℝ)|=(213806023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632147677/5000000000 : ℝ)|^8349 ≤ (10683365757071/25000000000000 : ℝ)^6301
        have hw : |(2632147677/5000000000 : ℝ)|=(2632147677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226143193/10000000000 : ℝ)|^8349 ≤ (2732245550929/20000000000000 : ℝ)^6301
        have hw : |(-2226143193/10000000000 : ℝ)|=(2226143193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362615817/10000000000 : ℝ)*x 0 + (846921977/2000000000 : ℝ)*x 1 + (449446033/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362615817/10000000000 : ℝ)^8349 ≤ (6663228780677/20000000000000 : ℝ)^6301 := by
    have hnat : (4362615817 : ℕ)^8349*20000000000000^6301 ≤ 6663228780677^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362615817 10000000000 6663228780677 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846921977/2000000000 : ℝ)^8349 ≤ (3202708405457/10000000000000 : ℝ)^6301 := by
    have hnat : (846921977 : ℕ)^8349*10000000000000^6301 ≤ 3202708405457^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846921977 2000000000 3202708405457 10000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449446033/1000000000 : ℝ)^8349 ≤ (34656772017859/100000000000000 : ℝ)^6301 := by
    have hnat : (449446033 : ℕ)^8349*100000000000000^6301 ≤ 34656772017859^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449446033 1000000000 34656772017859 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362615817/10000000000 : ℝ), (846921977/2000000000 : ℝ), (449446033/1000000000 : ℝ)] ![(6663228780677/20000000000000 : ℝ), (3202708405457/10000000000000 : ℝ), (34656772017859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362615817/10000000000 : ℝ)|^8349 ≤ (6663228780677/20000000000000 : ℝ)^6301
        have hw : |(4362615817/10000000000 : ℝ)|=(4362615817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846921977/2000000000 : ℝ)|^8349 ≤ (3202708405457/10000000000000 : ℝ)^6301
        have hw : |(846921977/2000000000 : ℝ)|=(846921977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449446033/1000000000 : ℝ)|^8349 ≤ (34656772017859/100000000000000 : ℝ)^6301
        have hw : |(449446033/1000000000 : ℝ)|=(449446033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-13500369/62500000 : ℝ)*x 0 + (5264631351/10000000000 : ℝ)*x 1 + (5394212989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13500369/62500000 : ℝ)^8349 ≤ (6563242772167/50000000000000 : ℝ)^6301 := by
    have hnat : (13500369 : ℕ)^8349*50000000000000^6301 ≤ 6563242772167^6301*62500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13500369 62500000 6563242772167 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264631351/10000000000 : ℝ)^8349 ≤ (21368538533193/50000000000000 : ℝ)^6301 := by
    have hnat : (5264631351 : ℕ)^8349*50000000000000^6301 ≤ 21368538533193^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264631351 10000000000 21368538533193 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394212989/10000000000 : ℝ)^8349 ≤ (8827287473537/20000000000000 : ℝ)^6301 := by
    have hnat : (5394212989 : ℕ)^8349*20000000000000^6301 ≤ 8827287473537^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394212989 10000000000 8827287473537 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13500369/62500000 : ℝ), (5264631351/10000000000 : ℝ), (5394212989/10000000000 : ℝ)] ![(6563242772167/50000000000000 : ℝ), (21368538533193/50000000000000 : ℝ), (8827287473537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13500369/62500000 : ℝ)|^8349 ≤ (6563242772167/50000000000000 : ℝ)^6301
        have hw : |(-13500369/62500000 : ℝ)|=(13500369/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264631351/10000000000 : ℝ)|^8349 ≤ (21368538533193/50000000000000 : ℝ)^6301
        have hw : |(5264631351/10000000000 : ℝ)|=(5264631351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394212989/10000000000 : ℝ)|^8349 ≤ (8827287473537/20000000000000 : ℝ)^6301
        have hw : |(5394212989/10000000000 : ℝ)|=(5394212989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312116341/10000000000 : ℝ)*x 0 + (-1048112751/5000000000 : ℝ)*x 1 + (1078842573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312116341/10000000000 : ℝ)^8349 ≤ (43248585768147/100000000000000 : ℝ)^6301 := by
    have hnat : (5312116341 : ℕ)^8349*100000000000000^6301 ≤ 43248585768147^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312116341 10000000000 43248585768147 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048112751/5000000000 : ℝ)^8349 ≤ (12614978197641/100000000000000 : ℝ)^6301 := by
    have hnat : (1048112751 : ℕ)^8349*100000000000000^6301 ≤ 12614978197641^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048112751 5000000000 12614978197641 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078842573/2000000000 : ℝ)^8349 ≤ (11034109005831/25000000000000 : ℝ)^6301 := by
    have hnat : (1078842573 : ℕ)^8349*25000000000000^6301 ≤ 11034109005831^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078842573 2000000000 11034109005831 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312116341/10000000000 : ℝ), (-1048112751/5000000000 : ℝ), (1078842573/2000000000 : ℝ)] ![(43248585768147/100000000000000 : ℝ), (12614978197641/100000000000000 : ℝ), (11034109005831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312116341/10000000000 : ℝ)|^8349 ≤ (43248585768147/100000000000000 : ℝ)^6301
        have hw : |(5312116341/10000000000 : ℝ)|=(5312116341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048112751/5000000000 : ℝ)|^8349 ≤ (12614978197641/100000000000000 : ℝ)^6301
        have hw : |(-1048112751/5000000000 : ℝ)|=(1048112751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078842573/2000000000 : ℝ)|^8349 ≤ (11034109005831/25000000000000 : ℝ)^6301
        have hw : |(1078842573/2000000000 : ℝ)|=(1078842573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062423321/2000000000 : ℝ)*x 0 + (1348553169/2500000000 : ℝ)*x 1 + (-2096225401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062423321/2000000000 : ℝ)^8349 ≤ (21624294308051/50000000000000 : ℝ)^6301 := by
    have hnat : (1062423321 : ℕ)^8349*50000000000000^6301 ≤ 21624294308051^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062423321 2000000000 21624294308051 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348553169/2500000000 : ℝ)^8349 ≤ (22068216987129/50000000000000 : ℝ)^6301 := by
    have hnat : (1348553169 : ℕ)^8349*50000000000000^6301 ≤ 22068216987129^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348553169 2500000000 22068216987129 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096225401/10000000000 : ℝ)^8349 ≤ (788436087017/6250000000000 : ℝ)^6301 := by
    have hnat : (2096225401 : ℕ)^8349*6250000000000^6301 ≤ 788436087017^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096225401 10000000000 788436087017 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062423321/2000000000 : ℝ), (1348553169/2500000000 : ℝ), (-2096225401/10000000000 : ℝ)] ![(21624294308051/50000000000000 : ℝ), (22068216987129/50000000000000 : ℝ), (788436087017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062423321/2000000000 : ℝ)|^8349 ≤ (21624294308051/50000000000000 : ℝ)^6301
        have hw : |(1062423321/2000000000 : ℝ)|=(1062423321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348553169/2500000000 : ℝ)|^8349 ≤ (22068216987129/50000000000000 : ℝ)^6301
        have hw : |(1348553169/2500000000 : ℝ)|=(1348553169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096225401/10000000000 : ℝ)|^8349 ≤ (788436087017/6250000000000 : ℝ)^6301
        have hw : |(-2096225401/10000000000 : ℝ)|=(2096225401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s5_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436262653/1000000000 : ℝ)*x 0 + (4493789723/10000000000 : ℝ)*x 1 + (16941131/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436262653/1000000000 : ℝ)^8349 ≤ (33316252307063/100000000000000 : ℝ)^6301 := by
    have hnat : (436262653 : ℕ)^8349*100000000000000^6301 ≤ 33316252307063^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436262653 1000000000 33316252307063 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493789723/10000000000 : ℝ)^8349 ≤ (34649920400667/100000000000000 : ℝ)^6301 := by
    have hnat : (4493789723 : ℕ)^8349*100000000000000^6301 ≤ 34649920400667^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493789723 10000000000 34649920400667 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16941131/40000000 : ℝ)^8349 ≤ (32033827286957/100000000000000 : ℝ)^6301 := by
    have hnat : (16941131 : ℕ)^8349*100000000000000^6301 ≤ 32033827286957^6301*40000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16941131 40000000 32033827286957 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436262653/1000000000 : ℝ), (4493789723/10000000000 : ℝ), (16941131/40000000 : ℝ)] ![(33316252307063/100000000000000 : ℝ), (34649920400667/100000000000000 : ℝ), (32033827286957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436262653/1000000000 : ℝ)|^8349 ≤ (33316252307063/100000000000000 : ℝ)^6301
        have hw : |(436262653/1000000000 : ℝ)|=(436262653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493789723/10000000000 : ℝ)|^8349 ≤ (34649920400667/100000000000000 : ℝ)^6301
        have hw : |(4493789723/10000000000 : ℝ)|=(4493789723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16941131/40000000 : ℝ)|^8349 ≤ (32033827286957/100000000000000 : ℝ)^6301
        have hw : |(16941131/40000000 : ℝ)|=(16941131/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1417/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5601/50000 : ℝ) ^ (2087/512 : ℝ) ≤ (3332002686328979/25000000000000000000 : ℝ) := by
    have hpowers : (5601/50000 : ℝ)^2087 ≤ (3332002686328979/25000000000000000000 : ℝ)^512 := by
      have hnat : (5601 : ℕ)^2087*25000000000000000000^512 ≤ 3332002686328979^512*50000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5601 50000 3332002686328979 25000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5601/50000 : ℝ)) (X := (3332002686328979/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (2087/512 : ℝ) ≤ (110608768951147/312500000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^2087 ≤ (110608768951147/312500000000000000 : ℝ)^512 := by
      have hnat : (2847 : ℕ)^2087*312500000000000000^512 ≤ 110608768951147^512*20000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 110608768951147 312500000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (110608768951147/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503332002686328979/12500000000000000000 : ℝ) ≤ (10000653881671097/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (12503332002686328979/12500000000000000000 : ℝ)^512 ≤ (10000653881671097/10000000000000000 : ℝ)^2087 := by
      have hnat : (12503332002686328979 : ℕ)^512*10000000000000000^2087 ≤ 10000653881671097^2087*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503332002686328979 12500000000000000000 10000653881671097 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000653881671097/10000000000000000 : ℝ)) (X := (12503332002686328979/12500000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012180704202420739/25000000000000000000 : ℝ) ≤ (10001195088510253/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (25012180704202420739/25000000000000000000 : ℝ)^512 ≤ (10001195088510253/10000000000000000 : ℝ)^2087 := by
      have hnat : (25012180704202420739 : ℕ)^512*10000000000000000^2087 ≤ 10001195088510253^2087*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012180704202420739 25000000000000000000 10001195088510253 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001195088510253/10000000000000000 : ℝ)) (X := (25012180704202420739/25000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (156360608768951147/156250000000000000 : ℝ) ≤ (10001736295349409/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (156360608768951147/156250000000000000 : ℝ)^512 ≤ (10001736295349409/10000000000000000 : ℝ)^2087 := by
      have hnat : (156360608768951147 : ℕ)^512*10000000000000000^2087 ≤ 10001736295349409^2087*156250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156360608768951147 156250000000000000 10001736295349409 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001736295349409/10000000000000000 : ℝ)) (X := (156360608768951147/156250000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3332002686328979/25000000000000000000 : ℝ) ≤ ((10106619341694662059/10110000000000000000 : ℝ)+2*(135301709789/75825000000000 : ℝ)*(5601/50000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (10106619341694662059/10110000000000000000 : ℝ)+2*(135301709789/75825000000000 : ℝ)*(5601/50000 : ℝ)=(10000653881671097/10000000000000000 : ℝ) by norm_num, show 1+2*(3332002686328979/25000000000000000000 : ℝ)=(12503332002686328979/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(110608768951147/312500000000000000 : ℝ)+(3332002686328979/25000000000000000000 : ℝ) ≤ ((10106619341694662059/10110000000000000000 : ℝ)+(135301709789/75825000000000 : ℝ)*((2847/20000 : ℝ)+(5601/50000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (10106619341694662059/10110000000000000000 : ℝ)+(135301709789/75825000000000 : ℝ)*((2847/20000 : ℝ)+(5601/50000 : ℝ))=(10001195088510253/10000000000000000 : ℝ) by norm_num, show 1+(110608768951147/312500000000000000 : ℝ)+(3332002686328979/25000000000000000000 : ℝ)=(25012180704202420739/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(110608768951147/312500000000000000 : ℝ) ≤ ((10106619341694662059/10110000000000000000 : ℝ)+2*(135301709789/75825000000000 : ℝ)*(2847/20000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (10106619341694662059/10110000000000000000 : ℝ)+2*(135301709789/75825000000000 : ℝ)*(2847/20000 : ℝ)=(10001736295349409/10000000000000000 : ℝ) by norm_num, show 1+2*(110608768951147/312500000000000000 : ℝ)=(156360608768951147/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10106619341694662059/10110000000000000000 : ℝ)*(X 1 0+X 2 0)+(135301709789/75825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (10106619341694662059/10110000000000000000 : ℝ)) (alpha := (135301709789/75825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10106619341694662059/10110000000000000000 : ℝ)*(X 0 1+X 2 1)+(135301709789/75825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (10106619341694662059/10110000000000000000 : ℝ)) (alpha := (135301709789/75825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10106619341694662059/10110000000000000000 : ℝ)*(X 0 2+X 1 2)+(135301709789/75825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (10106619341694662059/10110000000000000000 : ℝ)) (alpha := (135301709789/75825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135003353/625000000 : ℝ)*X 0 0+(5394550231/10000000000 : ℝ)*X 0 1+(5264295463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672575303/5000000000 : ℝ)*X 1 0+(-222614323/1000000000 : ℝ)*X 1 1+(41127307/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213806023/400000000 : ℝ)*X 2 0+(2632147677/5000000000 : ℝ)*X 2 1+(-2226143193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362615817/10000000000 : ℝ)*X 0 0+(846921977/2000000000 : ℝ)*X 0 1+(449446033/1000000000 : ℝ)*X 0 2+(4362615817/10000000000 : ℝ)*X 1 0+(846921977/2000000000 : ℝ)*X 1 1+(449446033/1000000000 : ℝ)*X 1 2+(4362615817/10000000000 : ℝ)*X 2 0+(846921977/2000000000 : ℝ)*X 2 1+(449446033/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-13500369/62500000 : ℝ)*X 0 0+(5264631351/10000000000 : ℝ)*X 0 1+(5394212989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312116341/10000000000 : ℝ)*X 1 0+(-1048112751/5000000000 : ℝ)*X 1 1+(1078842573/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062423321/2000000000 : ℝ)*X 2 0+(1348553169/2500000000 : ℝ)*X 2 1+(-2096225401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436262653/1000000000 : ℝ)*X 0 0+(4493789723/10000000000 : ℝ)*X 0 1+(16941131/40000000 : ℝ)*X 0 2+(436262653/1000000000 : ℝ)*X 1 0+(4493789723/10000000000 : ℝ)*X 1 1+(16941131/40000000 : ℝ)*X 1 2+(436262653/1000000000 : ℝ)*X 2 0+(4493789723/10000000000 : ℝ)*X 2 1+(16941131/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221448004487685181447565879/50550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54851331/100000000000000 : ℝ)*(base21) + (15549181/20000000000000 : ℝ)*(upper2) + (2714889/10000000000000 : ℝ)*(upper3) + (20194787/25000000000000 : ℝ)*(upper4) + (10167351/12500000000000 : ℝ)*(upper5) + (1152562713381673/20000000000000 : ℝ)*(major0) + (1152562713381673/20000000000000 : ℝ)*(major1) + (1152562713381673/20000000000000 : ℝ)*(major2) + (7677258797167499/100000000000000 : ℝ)*(sp0) + (7677246838884037/100000000000000 : ℝ)*(sp1) + (239913974298329/3125000000000 : ℝ)*(sp2) + (962092047655873/25000000000000 : ℝ)*(sp3) + (11958283463/100000000000000 : ℝ)*(sp5) + (11564769641/100000000000000 : ℝ)*(sp6) + (962092047655873/25000000000000 : ℝ)*(f.failure) + (7677258797167499/100000000000000 : ℝ)*(f.sum) + (914592074903/47390625000000000000000000 : ℝ)*base65 + (2443385603308534121/606600000000000000000000000000000 : ℝ)*base67 + (3716779305035734121/606600000000000000000000000000000 : ℝ)*base69 + (45264761175280534121/606600000000000000000000000000000 : ℝ)*base71 + (3874782750623/379125000000000000000000000 : ℝ)*base74 + (1858651641929734121/606600000000000000000000000000000 : ℝ)*base75 + (6501146545579465879/606600000000000000000000000000000 : ℝ)*base78 + (2992202125379134121/606600000000000000000000000000000 : ℝ)*base79 + (1596092891707/3033000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17877253/2500000000000000000000 : ℝ)*base90 + (17877253/2500000000000000000000 : ℝ)*base92 + (17877253/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317849637653660435167682421/33700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194927499/10000000000000 : ℝ)*(base19) + (1326706829/50000000000000 : ℝ)*(base23) + (140053229/100000000000000 : ℝ)*(upper2) + (85938569/50000000000000 : ℝ)*(upper3) + (171075481/50000000000000 : ℝ)*(upper5) + (1158551677018719/20000000000000 : ℝ)*(major0) + (1158551677018719/20000000000000 : ℝ)*(major1) + (1158551677018719/20000000000000 : ℝ)*(major2) + (48509586347/100000000000000 : ℝ)*(sp1) + (28835249609/50000000000000 : ℝ)*(sp2) + (7717151316730403/100000000000000 : ℝ)*(sp4) + (3858550428934533/50000000000000 : ℝ)*(sp5) + (3858545496408763/50000000000000 : ℝ)*(sp6) + (967091284766361/25000000000000 : ℝ)*(sp7) + (967091284766361/25000000000000 : ℝ)*(f.failure) + (7717151316730403/100000000000000 : ℝ)*(f.sum) + (669102123151/84250000000000000000000000 : ℝ)*base66 + (738398555954039193/67400000000000000000000000000000 : ℝ)*base68 + (297959715428839193/67400000000000000000000000000000 : ℝ)*base70 + (763393642307760807/67400000000000000000000000000000 : ℝ)*base71 + (1829111113397/168500000000000000000000000 : ℝ)*base74 + (85437623467839193/67400000000000000000000000000000 : ℝ)*base76 + (437403800073039193/67400000000000000000000000000000 : ℝ)*base78 + (1321781636962960807/67400000000000000000000000000000 : ℝ)*base79 + (948386980801/84250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14918979/2500000000000000000000 : ℝ)*base89 + (14918979/2500000000000000000000 : ℝ)*base91 + (14918979/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1156_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1156_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1156_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1156_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1156_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

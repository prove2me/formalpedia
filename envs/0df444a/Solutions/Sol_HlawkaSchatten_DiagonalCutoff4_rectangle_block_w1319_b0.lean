-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1319_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:55.828535+00:00
-- url     : https://prove2.me/submissions/0f4165cf-940e-4ba2-a80e-df44aaed3fbe

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
theorem support_rectangle_w1319_s0_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1822821509/10000000000 : ℝ)*x 0 + (3003454939/5000000000 : ℝ)*x 1 + (4805391881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1822821509/10000000000 : ℝ)^4279 ≤ (10670369926121/100000000000000 : ℝ)^3255 := by
    have hnat : (1822821509 : ℕ)^4279*100000000000000^3255 ≤ 10670369926121^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822821509 10000000000 10670369926121 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3003454939/5000000000 : ℝ)^4279 ≤ (25585053286563/50000000000000 : ℝ)^3255 := by
    have hnat : (3003454939 : ℕ)^4279*50000000000000^3255 ≤ 25585053286563^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003454939 5000000000 25585053286563 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4805391881/10000000000 : ℝ)^4279 ≤ (476994043649/1250000000000 : ℝ)^3255 := by
    have hnat : (4805391881 : ℕ)^4279*1250000000000^3255 ≤ 476994043649^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805391881 10000000000 476994043649 1250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1822821509/10000000000 : ℝ), (3003454939/5000000000 : ℝ), (4805391881/10000000000 : ℝ)] ![(10670369926121/100000000000000 : ℝ), (25585053286563/50000000000000 : ℝ), (476994043649/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1822821509/10000000000 : ℝ)|^4279 ≤ (10670369926121/100000000000000 : ℝ)^3255
        have hw : |(-1822821509/10000000000 : ℝ)|=(1822821509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3003454939/5000000000 : ℝ)|^4279 ≤ (25585053286563/50000000000000 : ℝ)^3255
        have hw : |(3003454939/5000000000 : ℝ)|=(3003454939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4805391881/10000000000 : ℝ)|^4279 ≤ (476994043649/1250000000000 : ℝ)^3255
        have hw : |(4805391881/10000000000 : ℝ)|=(4805391881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2752195103/5000000000 : ℝ)*x 0 + (-2506908609/10000000000 : ℝ)*x 1 + (480539197/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752195103/5000000000 : ℝ)^4279 ≤ (45618202020089/100000000000000 : ℝ)^3255 := by
    have hnat : (2752195103 : ℕ)^4279*100000000000000^3255 ≤ 45618202020089^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752195103 5000000000 45618202020089 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2506908609/10000000000 : ℝ)^4279 ≤ (16222273537259/100000000000000 : ℝ)^3255 := by
    have hnat : (2506908609 : ℕ)^4279*100000000000000^3255 ≤ 16222273537259^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506908609 10000000000 16222273537259 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480539197/1000000000 : ℝ)^4279 ≤ (7631904884201/20000000000000 : ℝ)^3255 := by
    have hnat : (480539197 : ℕ)^4279*20000000000000^3255 ≤ 7631904884201^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480539197 1000000000 7631904884201 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752195103/5000000000 : ℝ), (-2506908609/10000000000 : ℝ), (480539197/1000000000 : ℝ)] ![(45618202020089/100000000000000 : ℝ), (16222273537259/100000000000000 : ℝ), (7631904884201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752195103/5000000000 : ℝ)|^4279 ≤ (45618202020089/100000000000000 : ℝ)^3255
        have hw : |(2752195103/5000000000 : ℝ)|=(2752195103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2506908609/10000000000 : ℝ)|^4279 ≤ (16222273537259/100000000000000 : ℝ)^3255
        have hw : |(-2506908609/10000000000 : ℝ)|=(2506908609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(480539197/1000000000 : ℝ)|^4279 ≤ (7631904884201/20000000000000 : ℝ)^3255
        have hw : |(480539197/1000000000 : ℝ)|=(480539197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5504389443/10000000000 : ℝ)*x 0 + (600674053/1250000000 : ℝ)*x 1 + (-250690903/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504389443/10000000000 : ℝ)^4279 ≤ (22809096853669/50000000000000 : ℝ)^3255 := by
    have hnat : (5504389443 : ℕ)^4279*50000000000000^3255 ≤ 22809096853669^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504389443 10000000000 22809096853669 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600674053/1250000000 : ℝ)^4279 ≤ (19079764580191/50000000000000 : ℝ)^3255 := by
    have hnat : (600674053 : ℕ)^4279*50000000000000^3255 ≤ 19079764580191^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600674053 1250000000 19079764580191 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250690903/1000000000 : ℝ)^4279 ≤ (1013892319913/6250000000000 : ℝ)^3255 := by
    have hnat : (250690903 : ℕ)^4279*6250000000000^3255 ≤ 1013892319913^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250690903 1000000000 1013892319913 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504389443/10000000000 : ℝ), (600674053/1250000000 : ℝ), (-250690903/1000000000 : ℝ)] ![(22809096853669/50000000000000 : ℝ), (19079764580191/50000000000000 : ℝ), (1013892319913/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504389443/10000000000 : ℝ)|^4279 ≤ (22809096853669/50000000000000 : ℝ)^3255
        have hw : |(5504389443/10000000000 : ℝ)|=(5504389443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600674053/1250000000 : ℝ)|^4279 ≤ (19079764580191/50000000000000 : ℝ)^3255
        have hw : |(600674053/1250000000 : ℝ)|=(600674053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250690903/1000000000 : ℝ)|^4279 ≤ (1013892319913/6250000000000 : ℝ)^3255
        have hw : |(-250690903/1000000000 : ℝ)|=(250690903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182210617/10000000000 : ℝ)*x 0 + (3107787589/10000000000 : ℝ)*x 1 + (1400672941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182210617/10000000000 : ℝ)^4279 ≤ (1271636142301/4000000000000 : ℝ)^3255 := by
    have hnat : (4182210617 : ℕ)^4279*4000000000000^3255 ≤ 1271636142301^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182210617 10000000000 1271636142301 4000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107787589/10000000000 : ℝ)^4279 ≤ (10758459925389/50000000000000 : ℝ)^3255 := by
    have hnat : (3107787589 : ℕ)^4279*50000000000000^3255 ≤ 10758459925389^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107787589 10000000000 10758459925389 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1400672941/2500000000 : ℝ)^4279 ≤ (1167304414447/2500000000000 : ℝ)^3255 := by
    have hnat : (1400672941 : ℕ)^4279*2500000000000^3255 ≤ 1167304414447^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400672941 2500000000 1167304414447 2500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182210617/10000000000 : ℝ), (3107787589/10000000000 : ℝ), (1400672941/2500000000 : ℝ)] ![(1271636142301/4000000000000 : ℝ), (10758459925389/50000000000000 : ℝ), (1167304414447/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182210617/10000000000 : ℝ)|^4279 ≤ (1271636142301/4000000000000 : ℝ)^3255
        have hw : |(4182210617/10000000000 : ℝ)|=(4182210617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107787589/10000000000 : ℝ)|^4279 ≤ (10758459925389/50000000000000 : ℝ)^3255
        have hw : |(3107787589/10000000000 : ℝ)|=(3107787589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1400672941/2500000000 : ℝ)|^4279 ≤ (1167304414447/2500000000000 : ℝ)^3255
        have hw : |(1400672941/2500000000 : ℝ)|=(1400672941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-365480009/2000000000 : ℝ)*x 0 + (4836356693/10000000000 : ℝ)*x 1 + (1493710199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365480009/2000000000 : ℝ)^4279 ≤ (10705617133499/100000000000000 : ℝ)^3255 := by
    have hnat : (365480009 : ℕ)^4279*100000000000000^3255 ≤ 10705617133499^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365480009 2000000000 10705617133499 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4836356693/10000000000 : ℝ)^4279 ≤ (19241548589619/50000000000000 : ℝ)^3255 := by
    have hnat : (4836356693 : ℕ)^4279*50000000000000^3255 ≤ 19241548589619^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836356693 10000000000 19241548589619 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493710199/2500000000 : ℝ)^4279 ≤ (6351410709773/12500000000000 : ℝ)^3255 := by
    have hnat : (1493710199 : ℕ)^4279*12500000000000^3255 ≤ 6351410709773^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493710199 2500000000 6351410709773 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-365480009/2000000000 : ℝ), (4836356693/10000000000 : ℝ), (1493710199/2500000000 : ℝ)] ![(10705617133499/100000000000000 : ℝ), (19241548589619/50000000000000 : ℝ), (6351410709773/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-365480009/2000000000 : ℝ)|^4279 ≤ (10705617133499/100000000000000 : ℝ)^3255
        have hw : |(-365480009/2000000000 : ℝ)|=(365480009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4836356693/10000000000 : ℝ)|^4279 ≤ (19241548589619/50000000000000 : ℝ)^3255
        have hw : |(4836356693/10000000000 : ℝ)|=(4836356693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1493710199/2500000000 : ℝ)|^4279 ≤ (6351410709773/12500000000000 : ℝ)^3255
        have hw : |(1493710199/2500000000 : ℝ)|=(1493710199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2588545461/5000000000 : ℝ)*x 0 + (-1337460653/10000000000 : ℝ)*x 1 + (597484073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588545461/5000000000 : ℝ)^4279 ≤ (42086150397381/100000000000000 : ℝ)^3255 := by
    have hnat : (2588545461 : ℕ)^4279*100000000000000^3255 ≤ 42086150397381^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588545461 5000000000 42086150397381 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1337460653/10000000000 : ℝ)^4279 ≤ (7102564643803/100000000000000 : ℝ)^3255 := by
    have hnat : (1337460653 : ℕ)^4279*100000000000000^3255 ≤ 7102564643803^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337460653 10000000000 7102564643803 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597484073/1000000000 : ℝ)^4279 ≤ (50811284940333/100000000000000 : ℝ)^3255 := by
    have hnat : (597484073 : ℕ)^4279*100000000000000^3255 ≤ 50811284940333^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597484073 1000000000 50811284940333 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588545461/5000000000 : ℝ), (-1337460653/10000000000 : ℝ), (597484073/1000000000 : ℝ)] ![(42086150397381/100000000000000 : ℝ), (7102564643803/100000000000000 : ℝ), (50811284940333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588545461/5000000000 : ℝ)|^4279 ≤ (42086150397381/100000000000000 : ℝ)^3255
        have hw : |(2588545461/5000000000 : ℝ)|=(2588545461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1337460653/10000000000 : ℝ)|^4279 ≤ (7102564643803/100000000000000 : ℝ)^3255
        have hw : |(-1337460653/10000000000 : ℝ)|=(1337460653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597484073/1000000000 : ℝ)|^4279 ≤ (50811284940333/100000000000000 : ℝ)^3255
        have hw : |(597484073/1000000000 : ℝ)|=(597484073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5177090939/10000000000 : ℝ)*x 0 + (5974840769/10000000000 : ℝ)*x 1 + (-334365141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177090939/10000000000 : ℝ)^4279 ≤ (2630384411191/6250000000000 : ℝ)^3255 := by
    have hnat : (5177090939 : ℕ)^4279*6250000000000^3255 ≤ 2630384411191^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177090939 10000000000 2630384411191 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5974840769/10000000000 : ℝ)^4279 ≤ (3175705336021/6250000000000 : ℝ)^3255 := by
    have hnat : (5974840769 : ℕ)^4279*6250000000000^3255 ≤ 3175705336021^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974840769 10000000000 3175705336021 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334365141/2500000000 : ℝ)^4279 ≤ (7102564022483/100000000000000 : ℝ)^3255 := by
    have hnat : (334365141 : ℕ)^4279*100000000000000^3255 ≤ 7102564022483^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334365141 2500000000 7102564022483 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177090939/10000000000 : ℝ), (5974840769/10000000000 : ℝ), (-334365141/2500000000 : ℝ)] ![(2630384411191/6250000000000 : ℝ), (3175705336021/6250000000000 : ℝ), (7102564022483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177090939/10000000000 : ℝ)|^4279 ≤ (2630384411191/6250000000000 : ℝ)^3255
        have hw : |(5177090939/10000000000 : ℝ)|=(5177090939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5974840769/10000000000 : ℝ)|^4279 ≤ (3175705336021/6250000000000 : ℝ)^3255
        have hw : |(5974840769/10000000000 : ℝ)|=(5974840769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334365141/2500000000 : ℝ)|^4279 ≤ (7102564022483/100000000000000 : ℝ)^3255
        have hw : |(-334365141/2500000000 : ℝ)|=(334365141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s0_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095858559/5000000000 : ℝ)*x 0 + (5538395131/10000000000 : ℝ)*x 1 + (396797131/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095858559/5000000000 : ℝ)^4279 ≤ (15942967151463/50000000000000 : ℝ)^3255 := by
    have hnat : (2095858559 : ℕ)^4279*50000000000000^3255 ≤ 15942967151463^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095858559 5000000000 15942967151463 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5538395131/10000000000 : ℝ)^4279 ≤ (22994519608613/50000000000000 : ℝ)^3255 := by
    have hnat : (5538395131 : ℕ)^4279*50000000000000^3255 ≤ 22994519608613^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538395131 10000000000 22994519608613 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396797131/1250000000 : ℝ)^4279 ≤ (2765628309259/12500000000000 : ℝ)^3255 := by
    have hnat : (396797131 : ℕ)^4279*12500000000000^3255 ≤ 2765628309259^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396797131 1250000000 2765628309259 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095858559/5000000000 : ℝ), (5538395131/10000000000 : ℝ), (396797131/1250000000 : ℝ)] ![(15942967151463/50000000000000 : ℝ), (22994519608613/50000000000000 : ℝ), (2765628309259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095858559/5000000000 : ℝ)|^4279 ≤ (15942967151463/50000000000000 : ℝ)^3255
        have hw : |(2095858559/5000000000 : ℝ)|=(2095858559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5538395131/10000000000 : ℝ)|^4279 ≤ (22994519608613/50000000000000 : ℝ)^3255
        have hw : |(5538395131/10000000000 : ℝ)|=(5538395131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396797131/1250000000 : ℝ)|^4279 ≤ (2765628309259/12500000000000 : ℝ)^3255
        have hw : |(396797131/1250000000 : ℝ)|=(396797131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (31/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13519/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2139/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2139 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2139*1^512 ≤ 0^512*1^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2139/512 : ℝ) ≤ (2175265873900264751/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2139 ≤ (2175265873900264751/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2139*100000000000000000000^512 ≤ 2175265873900264751^512*5^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2175265873900264751 100000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2175265873900264751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2139 := by
      have hnat : (1 : ℕ)^512*1^2139 ≤ 1^2139*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102175265873900264751/100000000000000000000 : ℝ) ≤ (402065709508123/400000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (102175265873900264751/100000000000000000000 : ℝ)^512 ≤ (402065709508123/400000000000000 : ℝ)^2139 := by
      have hnat : (102175265873900264751 : ℕ)^512*400000000000000^2139 ≤ 402065709508123^2139*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102175265873900264751 100000000000000000000 402065709508123 400000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402065709508123/400000000000000 : ℝ)) (X := (102175265873900264751/100000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52175265873900264751/50000000000000000000 : ℝ) ≤ (202065709508123/200000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (52175265873900264751/50000000000000000000 : ℝ)^512 ≤ (202065709508123/200000000000000 : ℝ)^2139 := by
      have hnat : (52175265873900264751 : ℕ)^512*200000000000000^2139 ≤ 202065709508123^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52175265873900264751 50000000000000000000 202065709508123 200000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202065709508123/200000000000000 : ℝ)) (X := (52175265873900264751/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2065709508123/160000000000000 : ℝ)*(0 : ℝ))^(2139/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(2065709508123/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2175265873900264751/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2065709508123/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (1 : ℝ)+(2065709508123/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(402065709508123/400000000000000 : ℝ) by norm_num, show 1+(2175265873900264751/100000000000000000000 : ℝ)+(0 : ℝ)=(102175265873900264751/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2175265873900264751/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2065709508123/160000000000000 : ℝ)*(2/5 : ℝ))^(2139/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(2065709508123/160000000000000 : ℝ)*(2/5 : ℝ)=(202065709508123/200000000000000 : ℝ) by norm_num, show 1+2*(2175265873900264751/100000000000000000000 : ℝ)=(52175265873900264751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2065709508123/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2065709508123/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2065709508123/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2065709508123/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2065709508123/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2065709508123/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1822821509/10000000000 : ℝ)*X 0 0+(3003454939/5000000000 : ℝ)*X 0 1+(4805391881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2752195103/5000000000 : ℝ)*X 1 0+(-2506908609/10000000000 : ℝ)*X 1 1+(480539197/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5504389443/10000000000 : ℝ)*X 2 0+(600674053/1250000000 : ℝ)*X 2 1+(-250690903/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4182210617/10000000000 : ℝ)*X 0 0+(3107787589/10000000000 : ℝ)*X 0 1+(1400672941/2500000000 : ℝ)*X 0 2+(4182210617/10000000000 : ℝ)*X 1 0+(3107787589/10000000000 : ℝ)*X 1 1+(1400672941/2500000000 : ℝ)*X 1 2+(4182210617/10000000000 : ℝ)*X 2 0+(3107787589/10000000000 : ℝ)*X 2 1+(1400672941/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-365480009/2000000000 : ℝ)*X 0 0+(4836356693/10000000000 : ℝ)*X 0 1+(1493710199/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588545461/5000000000 : ℝ)*X 1 0+(-1337460653/10000000000 : ℝ)*X 1 1+(597484073/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5177090939/10000000000 : ℝ)*X 2 0+(5974840769/10000000000 : ℝ)*X 2 1+(-334365141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2095858559/5000000000 : ℝ)*X 0 0+(5538395131/10000000000 : ℝ)*X 0 1+(396797131/1250000000 : ℝ)*X 0 2+(2095858559/5000000000 : ℝ)*X 1 0+(5538395131/10000000000 : ℝ)*X 1 1+(396797131/1250000000 : ℝ)*X 1 2+(2095858559/5000000000 : ℝ)*X 2 0+(5538395131/10000000000 : ℝ)*X 2 1+(396797131/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (964910498742440027577/160000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88124941/100000000000000 : ℝ)*(base1) + (153702523/10000000000000 : ℝ)*(base19) + (284331231/20000000000000 : ℝ)*(base23) + (115350611/50000000000000 : ℝ)*(upper3) + (21798167/25000000000000 : ℝ)*(upper5) + (12331121057891/2000000000000 : ℝ)*(major0) + (12331121057891/2000000000000 : ℝ)*(major1) + (12331121057891/2000000000000 : ℝ)*(major2) + (832285827514713/100000000000000 : ℝ)*(sp0) + (166457751642311/20000000000000 : ℝ)*(sp1) + (832288873580631/100000000000000 : ℝ)*(sp2) + (80163806942031/20000000000000 : ℝ)*(sp3) + (4555847013/100000000000000 : ℝ)*(sp4) + (248669419/10000000000000 : ℝ)*(sp7) + (80164321905857/20000000000000 : ℝ)*(f.failure) + (416145147618393/50000000000000 : ℝ)*(f.sum) + (538691459887/160000000000000000000000000 : ℝ)*base66 + (709349677967/320000000000000000000000000 : ℝ)*base68 + (1171577095473/320000000000000000000000000 : ℝ)*base69 + (183132825393/320000000000000000000000000 : ℝ)*base71 + (803858761807/160000000000000000000000000 : ℝ)*base74 + (2421872823793/320000000000000000000000000 : ℝ)*base75 + (286514599567/320000000000000000000000000 : ℝ)*base78 + (915396564687/320000000000000000000000000 : ℝ)*base80 + (477320909007/160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10055151/2000000000000000000000 : ℝ)*base90 + (10055151/2000000000000000000000 : ℝ)*base92 + (10055151/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7078541106254043895899/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1053306251/50000000000000 : ℝ)*(base19) + (2129244973/100000000000000 : ℝ)*(base23) + (51577631/50000000000000 : ℝ)*(base32) + (147103319/50000000000000 : ℝ)*(upper3) + (42280367/20000000000000 : ℝ)*(upper5) + (325342316120629/50000000000000 : ℝ)*(major0) + (325342316120629/50000000000000 : ℝ)*(major1) + (325342316120629/50000000000000 : ℝ)*(major2) + (4685466223/100000000000000 : ℝ)*(sp1) + (312365469/6250000000000 : ℝ)*(sp2) + (21959011313233/2500000000000 : ℝ)*(sp4) + (219588415112649/25000000000000 : ℝ)*(sp5) + (878353325436843/100000000000000 : ℝ)*(sp6) + (42300841385871/10000000000000 : ℝ)*(sp7) + (105752129253493/25000000000000 : ℝ)*(f.failure) + (21959011313233/2500000000000 : ℝ)*(f.sum) + (8470809849367/4000000000000000000000000000 : ℝ)*base65 + (54531685209367/8000000000000000000000000000 : ℝ)*base67 + (48816908969367/8000000000000000000000000000 : ℝ)*base69 + (1733129529367/8000000000000000000000000000 : ℝ)*base71 + (36632611309367/4000000000000000000000000000 : ℝ)*base73 + (49758016390633/8000000000000000000000000000 : ℝ)*base76 + (22153414337367/8000000000000000000000000000 : ℝ)*base77 + (48457899585367/8000000000000000000000000000 : ℝ)*base79 + (21252453337367/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (28811899/2500000000000000000000 : ℝ)*base90 + (28811899/2500000000000000000000 : ℝ)*base92 + (28811899/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1319_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (31/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13519/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1319_s1_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-62842363/312500000 : ℝ)*x 0 + (2826310371/5000000000 : ℝ)*x 1 + (1259804703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62842363/312500000 : ℝ)^4279 ≤ (242821884399/2000000000000 : ℝ)^3255 := by
    have hnat : (62842363 : ℕ)^4279*2000000000000^3255 ≤ 242821884399^3255*312500000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62842363 312500000 242821884399 2000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2826310371/5000000000 : ℝ)^4279 ≤ (2361997343707/5000000000000 : ℝ)^3255 := by
    have hnat : (2826310371 : ℕ)^4279*5000000000000^3255 ≤ 2361997343707^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826310371 5000000000 2361997343707 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259804703/2500000000 : ℝ)^4279 ≤ (5077369860447/12500000000000 : ℝ)^3255 := by
    have hnat : (1259804703 : ℕ)^4279*12500000000000^3255 ≤ 5077369860447^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259804703 2500000000 5077369860447 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62842363/312500000 : ℝ), (2826310371/5000000000 : ℝ), (1259804703/2500000000 : ℝ)] ![(242821884399/2000000000000 : ℝ), (2361997343707/5000000000000 : ℝ), (5077369860447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62842363/312500000 : ℝ)|^4279 ≤ (242821884399/2000000000000 : ℝ)^3255
        have hw : |(-62842363/312500000 : ℝ)|=(62842363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2826310371/5000000000 : ℝ)|^4279 ≤ (2361997343707/5000000000000 : ℝ)^3255
        have hw : |(2826310371/5000000000 : ℝ)|=(2826310371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1259804703/2500000000 : ℝ)|^4279 ≤ (5077369860447/12500000000000 : ℝ)^3255
        have hw : |(1259804703/2500000000 : ℝ)|=(1259804703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408131559/10000000000 : ℝ)*x 0 + (-292366951/1250000000 : ℝ)*x 1 + (251960941/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408131559/10000000000 : ℝ)^4279 ≤ (44572377311327/100000000000000 : ℝ)^3255 := by
    have hnat : (5408131559 : ℕ)^4279*100000000000000^3255 ≤ 44572377311327^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408131559 10000000000 44572377311327 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292366951/1250000000 : ℝ)^4279 ≤ (14808663700541/100000000000000 : ℝ)^3255 := by
    have hnat : (292366951 : ℕ)^4279*100000000000000^3255 ≤ 14808663700541^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292366951 1250000000 14808663700541 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251960941/500000000 : ℝ)^4279 ≤ (20309479484173/50000000000000 : ℝ)^3255 := by
    have hnat : (251960941 : ℕ)^4279*50000000000000^3255 ≤ 20309479484173^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251960941 500000000 20309479484173 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408131559/10000000000 : ℝ), (-292366951/1250000000 : ℝ), (251960941/500000000 : ℝ)] ![(44572377311327/100000000000000 : ℝ), (14808663700541/100000000000000 : ℝ), (20309479484173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408131559/10000000000 : ℝ)|^4279 ≤ (44572377311327/100000000000000 : ℝ)^3255
        have hw : |(5408131559/10000000000 : ℝ)|=(5408131559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292366951/1250000000 : ℝ)|^4279 ≤ (14808663700541/100000000000000 : ℝ)^3255
        have hw : |(-292366951/1250000000 : ℝ)|=(292366951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251960941/500000000 : ℝ)|^4279 ≤ (20309479484173/50000000000000 : ℝ)^3255
        have hw : |(251960941/500000000 : ℝ)|=(251960941/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (338008219/625000000 : ℝ)*x 0 + (5039218741/10000000000 : ℝ)*x 1 + (-116946789/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338008219/625000000 : ℝ)^4279 ≤ (44572376715429/100000000000000 : ℝ)^3255 := by
    have hnat : (338008219 : ℕ)^4279*100000000000000^3255 ≤ 44572376715429^3255*625000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338008219 625000000 44572376715429 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5039218741/10000000000 : ℝ)^4279 ≤ (20309479065617/50000000000000 : ℝ)^3255 := by
    have hnat : (5039218741 : ℕ)^4279*50000000000000^3255 ≤ 20309479065617^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039218741 10000000000 20309479065617 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116946789/500000000 : ℝ)^4279 ≤ (14808665132127/100000000000000 : ℝ)^3255 := by
    have hnat : (116946789 : ℕ)^4279*100000000000000^3255 ≤ 14808665132127^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116946789 500000000 14808665132127 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338008219/625000000 : ℝ), (5039218741/10000000000 : ℝ), (-116946789/500000000 : ℝ)] ![(44572376715429/100000000000000 : ℝ), (20309479065617/50000000000000 : ℝ), (14808665132127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338008219/625000000 : ℝ)|^4279 ≤ (44572376715429/100000000000000 : ℝ)^3255
        have hw : |(338008219/625000000 : ℝ)|=(338008219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5039218741/10000000000 : ℝ)|^4279 ≤ (20309479065617/50000000000000 : ℝ)^3255
        have hw : |(5039218741/10000000000 : ℝ)|=(5039218741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116946789/500000000 : ℝ)|^4279 ≤ (14808665132127/100000000000000 : ℝ)^3255
        have hw : |(-116946789/500000000 : ℝ)|=(116946789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296387369/10000000000 : ℝ)*x 0 + (925929969/2500000000 : ℝ)*x 1 + (199096997/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296387369/10000000000 : ℝ)^4279 ≤ (32936721156899/100000000000000 : ℝ)^3255 := by
    have hnat : (4296387369 : ℕ)^4279*100000000000000^3255 ≤ 32936721156899^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296387369 10000000000 32936721156899 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925929969/2500000000 : ℝ)^4279 ≤ (27097843897469/100000000000000 : ℝ)^3255 := by
    have hnat : (925929969 : ℕ)^4279*100000000000000^3255 ≤ 27097843897469^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925929969 2500000000 27097843897469 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199096997/400000000 : ℝ)^4279 ≤ (9991358731871/25000000000000 : ℝ)^3255 := by
    have hnat : (199096997 : ℕ)^4279*25000000000000^3255 ≤ 9991358731871^3255*400000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199096997 400000000 9991358731871 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296387369/10000000000 : ℝ), (925929969/2500000000 : ℝ), (199096997/400000000 : ℝ)] ![(32936721156899/100000000000000 : ℝ), (27097843897469/100000000000000 : ℝ), (9991358731871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296387369/10000000000 : ℝ)|^4279 ≤ (32936721156899/100000000000000 : ℝ)^3255
        have hw : |(4296387369/10000000000 : ℝ)|=(4296387369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925929969/2500000000 : ℝ)|^4279 ≤ (27097843897469/100000000000000 : ℝ)^3255
        have hw : |(925929969/2500000000 : ℝ)|=(925929969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199096997/400000000 : ℝ)|^4279 ≤ (9991358731871/25000000000000 : ℝ)^3255
        have hw : |(199096997/400000000 : ℝ)|=(199096997/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2011536303/10000000000 : ℝ)*x 0 + (315440793/625000000 : ℝ)*x 1 + (35279011/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011536303/10000000000 : ℝ)^4279 ≤ (12145703238601/100000000000000 : ℝ)^3255 := by
    have hnat : (2011536303 : ℕ)^4279*100000000000000^3255 ≤ 12145703238601^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011536303 10000000000 12145703238601 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315440793/625000000 : ℝ)^4279 ≤ (8140397955171/20000000000000 : ℝ)^3255 := by
    have hnat : (315440793 : ℕ)^4279*20000000000000^3255 ≤ 8140397955171^3255*625000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315440793 625000000 8140397955171 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35279011/62500000 : ℝ)^4279 ≤ (9430461395273/20000000000000 : ℝ)^3255 := by
    have hnat : (35279011 : ℕ)^4279*20000000000000^3255 ≤ 9430461395273^3255*62500000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35279011 62500000 9430461395273 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2011536303/10000000000 : ℝ), (315440793/625000000 : ℝ), (35279011/62500000 : ℝ)] ![(12145703238601/100000000000000 : ℝ), (8140397955171/20000000000000 : ℝ), (9430461395273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2011536303/10000000000 : ℝ)|^4279 ≤ (12145703238601/100000000000000 : ℝ)^3255
        have hw : |(-2011536303/10000000000 : ℝ)|=(2011536303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(315440793/625000000 : ℝ)|^4279 ≤ (8140397955171/20000000000000 : ℝ)^3255
        have hw : |(315440793/625000000 : ℝ)|=(315440793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35279011/62500000 : ℝ)|^4279 ≤ (9430461395273/20000000000000 : ℝ)^3255
        have hw : |(35279011/62500000 : ℝ)|=(35279011/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524927297/1000000000 : ℝ)*x 0 + (-346702623/2000000000 : ℝ)*x 1 + (5644641399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524927297/1000000000 : ℝ)^4279 ≤ (42859226611833/100000000000000 : ℝ)^3255 := by
    have hnat : (524927297 : ℕ)^4279*100000000000000^3255 ≤ 42859226611833^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524927297 1000000000 42859226611833 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346702623/2000000000 : ℝ)^4279 ≤ (1997694071449/20000000000000 : ℝ)^3255 := by
    have hnat : (346702623 : ℕ)^4279*20000000000000^3255 ≤ 1997694071449^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346702623 2000000000 1997694071449 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644641399/10000000000 : ℝ)^4279 ≤ (23576151506039/50000000000000 : ℝ)^3255 := by
    have hnat : (5644641399 : ℕ)^4279*50000000000000^3255 ≤ 23576151506039^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644641399 10000000000 23576151506039 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524927297/1000000000 : ℝ), (-346702623/2000000000 : ℝ), (5644641399/10000000000 : ℝ)] ![(42859226611833/100000000000000 : ℝ), (1997694071449/20000000000000 : ℝ), (23576151506039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524927297/1000000000 : ℝ)|^4279 ≤ (42859226611833/100000000000000 : ℝ)^3255
        have hw : |(524927297/1000000000 : ℝ)|=(524927297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346702623/2000000000 : ℝ)|^4279 ≤ (1997694071449/20000000000000 : ℝ)^3255
        have hw : |(-346702623/2000000000 : ℝ)|=(346702623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5644641399/10000000000 : ℝ)|^4279 ≤ (23576151506039/50000000000000 : ℝ)^3255
        have hw : |(5644641399/10000000000 : ℝ)|=(5644641399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656159101/1250000000 : ℝ)*x 0 + (5644641241/10000000000 : ℝ)*x 1 + (-866756787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656159101/1250000000 : ℝ)^4279 ≤ (1714368994921/4000000000000 : ℝ)^3255 := by
    have hnat : (656159101 : ℕ)^4279*4000000000000^3255 ≤ 1714368994921^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656159101 1250000000 1714368994921 4000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5644641241/10000000000 : ℝ)^4279 ≤ (5894037659627/12500000000000 : ℝ)^3255 := by
    have hnat : (5644641241 : ℕ)^4279*12500000000000^3255 ≤ 5894037659627^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644641241 10000000000 5894037659627 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866756787/5000000000 : ℝ)^4279 ≤ (4994236917007/50000000000000 : ℝ)^3255 := by
    have hnat : (866756787 : ℕ)^4279*50000000000000^3255 ≤ 4994236917007^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866756787 5000000000 4994236917007 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656159101/1250000000 : ℝ), (5644641241/10000000000 : ℝ), (-866756787/5000000000 : ℝ)] ![(1714368994921/4000000000000 : ℝ), (5894037659627/12500000000000 : ℝ), (4994236917007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656159101/1250000000 : ℝ)|^4279 ≤ (1714368994921/4000000000000 : ℝ)^3255
        have hw : |(656159101/1250000000 : ℝ)|=(656159101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5644641241/10000000000 : ℝ)|^4279 ≤ (5894037659627/12500000000000 : ℝ)^3255
        have hw : |(5644641241/10000000000 : ℝ)|=(5644641241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-866756787/5000000000 : ℝ)|^4279 ≤ (4994236917007/50000000000000 : ℝ)^3255
        have hw : |(-866756787/5000000000 : ℝ)|=(866756787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s1_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429759257/1000000000 : ℝ)*x 0 + (62014471/125000000 : ℝ)*x 1 + (3720288599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429759257/1000000000 : ℝ)^4279 ≤ (3294886753707/10000000000000 : ℝ)^3255 := by
    have hnat : (429759257 : ℕ)^4279*10000000000000^3255 ≤ 3294886753707^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429759257 1000000000 3294886753707 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62014471/125000000 : ℝ)^4279 ≤ (19896908699901/50000000000000 : ℝ)^3255 := by
    have hnat : (62014471 : ℕ)^4279*50000000000000^3255 ≤ 19896908699901^3255*125000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62014471 125000000 19896908699901 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3720288599/10000000000 : ℝ)^4279 ≤ (2725731504411/10000000000000 : ℝ)^3255 := by
    have hnat : (3720288599 : ℕ)^4279*10000000000000^3255 ≤ 2725731504411^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720288599 10000000000 2725731504411 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429759257/1000000000 : ℝ), (62014471/125000000 : ℝ), (3720288599/10000000000 : ℝ)] ![(3294886753707/10000000000000 : ℝ), (19896908699901/50000000000000 : ℝ), (2725731504411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429759257/1000000000 : ℝ)|^4279 ≤ (3294886753707/10000000000000 : ℝ)^3255
        have hw : |(429759257/1000000000 : ℝ)|=(429759257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62014471/125000000 : ℝ)|^4279 ≤ (19896908699901/50000000000000 : ℝ)^3255
        have hw : |(62014471/125000000 : ℝ)|=(62014471/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3720288599/10000000000 : ℝ)|^4279 ≤ (2725731504411/10000000000000 : ℝ)^3255
        have hw : |(3720288599/10000000000 : ℝ)|=(3720288599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13519/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (417/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19637/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13519/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (31/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13519/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (31/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13519/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (31/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13519/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (31/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13519/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (31/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13519/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (31/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (31/2500 : ℝ) ^ (2139/512 : ℝ) ≤ (1083483334067/100000000000000000000 : ℝ) := by
    have hpowers : (31/2500 : ℝ)^2139 ≤ (1083483334067/100000000000000000000 : ℝ)^512 := by
      have hnat : (31 : ℕ)^2139*100000000000000000000^512 ≤ 1083483334067^512*2500^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31 2500 1083483334067 100000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31/2500 : ℝ)) (X := (1083483334067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13519/50000 : ℝ) ^ (2139/512 : ℝ) ≤ (84717007113729503/20000000000000000000 : ℝ) := by
    have hpowers : (13519/50000 : ℝ)^2139 ≤ (84717007113729503/20000000000000000000 : ℝ)^512 := by
      have hnat : (13519 : ℕ)^2139*20000000000000000000^512 ≤ 84717007113729503^512*50000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13519 50000 84717007113729503 20000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13519/50000 : ℝ)) (X := (84717007113729503/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001083483334067/50000000000000000000 : ℝ) ≤ (5000000025934711/5000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50000001083483334067/50000000000000000000 : ℝ)^512 ≤ (5000000025934711/5000000000000000 : ℝ)^2139 := by
      have hnat : (50000001083483334067 : ℕ)^512*5000000000000000^2139 ≤ 5000000025934711^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001083483334067 50000000000000000000 5000000025934711 5000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000025934711/5000000000000000 : ℝ)) (X := (50000001083483334067/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50211793059525990791/50000000000000000000 : ℝ) ≤ (10010122841386091/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50211793059525990791/50000000000000000000 : ℝ)^512 ≤ (10010122841386091/10000000000000000 : ℝ)^2139 := by
      have hnat : (50211793059525990791 : ℕ)^512*10000000000000000^2139 ≤ 10010122841386091^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50211793059525990791 50000000000000000000 10010122841386091 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010122841386091/10000000000000000 : ℝ)) (X := (50211793059525990791/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10084717007113729503/10000000000000000000 : ℝ) ≤ (250506140772569/250000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (10084717007113729503/10000000000000000000 : ℝ)^512 ≤ (250506140772569/250000000000000 : ℝ)^2139 := by
      have hnat : (10084717007113729503 : ℕ)^512*250000000000000^2139 ≤ 250506140772569^2139*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10084717007113729503 10000000000000000000 250506140772569 250000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250506140772569/250000000000000 : ℝ)) (X := (10084717007113729503/10000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1083483334067/100000000000000000000 : ℝ) ≤ ((64488724205031502409/64495000000000000000 : ℝ)+2*(10122789516669/2579800000000000 : ℝ)*(31/2500 : ℝ))^(2139/512 : ℝ) := by
    rw [show (64488724205031502409/64495000000000000000 : ℝ)+2*(10122789516669/2579800000000000 : ℝ)*(31/2500 : ℝ)=(5000000025934711/5000000000000000 : ℝ) by norm_num, show 1+2*(1083483334067/100000000000000000000 : ℝ)=(50000001083483334067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(84717007113729503/20000000000000000000 : ℝ)+(1083483334067/100000000000000000000 : ℝ) ≤ ((64488724205031502409/64495000000000000000 : ℝ)+(10122789516669/2579800000000000 : ℝ)*((13519/50000 : ℝ)+(31/2500 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (64488724205031502409/64495000000000000000 : ℝ)+(10122789516669/2579800000000000 : ℝ)*((13519/50000 : ℝ)+(31/2500 : ℝ))=(10010122841386091/10000000000000000 : ℝ) by norm_num, show 1+(84717007113729503/20000000000000000000 : ℝ)+(1083483334067/100000000000000000000 : ℝ)=(50211793059525990791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(84717007113729503/20000000000000000000 : ℝ) ≤ ((64488724205031502409/64495000000000000000 : ℝ)+2*(10122789516669/2579800000000000 : ℝ)*(13519/50000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (64488724205031502409/64495000000000000000 : ℝ)+2*(10122789516669/2579800000000000 : ℝ)*(13519/50000 : ℝ)=(250506140772569/250000000000000 : ℝ) by norm_num, show 1+2*(84717007113729503/20000000000000000000 : ℝ)=(10084717007113729503/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64488724205031502409/64495000000000000000 : ℝ)*(X 1 0+X 2 0)+(10122789516669/2579800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (31/2500 : ℝ)) (hi := (13519/50000 : ℝ)) (c := (64488724205031502409/64495000000000000000 : ℝ)) (alpha := (10122789516669/2579800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64488724205031502409/64495000000000000000 : ℝ)*(X 0 1+X 2 1)+(10122789516669/2579800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (31/2500 : ℝ)) (hi := (13519/50000 : ℝ)) (c := (64488724205031502409/64495000000000000000 : ℝ)) (alpha := (10122789516669/2579800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64488724205031502409/64495000000000000000 : ℝ)*(X 0 2+X 1 2)+(10122789516669/2579800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (31/2500 : ℝ)) (hi := (13519/50000 : ℝ)) (c := (64488724205031502409/64495000000000000000 : ℝ)) (alpha := (10122789516669/2579800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-62842363/312500000 : ℝ)*X 0 0+(2826310371/5000000000 : ℝ)*X 0 1+(1259804703/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5408131559/10000000000 : ℝ)*X 1 0+(-292366951/1250000000 : ℝ)*X 1 1+(251960941/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338008219/625000000 : ℝ)*X 2 0+(5039218741/10000000000 : ℝ)*X 2 1+(-116946789/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296387369/10000000000 : ℝ)*X 0 0+(925929969/2500000000 : ℝ)*X 0 1+(199096997/400000000 : ℝ)*X 0 2+(4296387369/10000000000 : ℝ)*X 1 0+(925929969/2500000000 : ℝ)*X 1 1+(199096997/400000000 : ℝ)*X 1 2+(4296387369/10000000000 : ℝ)*X 2 0+(925929969/2500000000 : ℝ)*X 2 1+(199096997/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2011536303/10000000000 : ℝ)*X 0 0+(315440793/625000000 : ℝ)*X 0 1+(35279011/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((524927297/1000000000 : ℝ)*X 1 0+(-346702623/2000000000 : ℝ)*X 1 1+(5644641399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656159101/1250000000 : ℝ)*X 2 0+(5644641241/10000000000 : ℝ)*X 2 1+(-866756787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429759257/1000000000 : ℝ)*X 0 0+(62014471/125000000 : ℝ)*X 0 1+(3720288599/10000000000 : ℝ)*X 0 2+(429759257/1000000000 : ℝ)*X 1 0+(62014471/125000000 : ℝ)*X 1 1+(3720288599/10000000000 : ℝ)*X 1 2+(429759257/1000000000 : ℝ)*X 2 0+(62014471/125000000 : ℝ)*X 2 1+(3720288599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (590900915634037995123907983/64495000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1163873/1250000000000 : ℝ)*(base1) + (1775806717/100000000000000 : ℝ)*(base19) + (1759227073/100000000000000 : ℝ)*(base23) + (239748549/100000000000000 : ℝ)*(upper3) + (83538601/50000000000000 : ℝ)*(upper5) + (24153937705257/2000000000000 : ℝ)*(major0) + (24153937705257/2000000000000 : ℝ)*(major1) + (24153937705257/2000000000000 : ℝ)*(major2) + (815131437843747/50000000000000 : ℝ)*(sp0) + (203783855512421/12500000000000 : ℝ)*(sp1) + (407567715169753/25000000000000 : ℝ)*(sp2) + (785115712066031/100000000000000 : ℝ)*(sp3) + (983732843/10000000000000 : ℝ)*(sp4) + (1008008983/20000000000000 : ℝ)*(sp7) + (157024169044157/20000000000000 : ℝ)*(f.failure) + (326054523981217/20000000000000 : ℝ)*(f.sum) + (263504253343/161237500000000000000000000 : ℝ)*base66 + (412048028772229113/128990000000000000000000000000000 : ℝ)*base67 + (593102140705669113/128990000000000000000000000000000 : ℝ)*base69 + (108850718808799113/128990000000000000000000000000000 : ℝ)*base71 + (58196570616523/12899000000000000000000000000 : ℝ)*base74 + (442889179695989113/128990000000000000000000000000000 : ℝ)*base75 + (287367804858159113/128990000000000000000000000000000 : ℝ)*base77 + (954961327191269113/128990000000000000000000000000000 : ℝ)*base79 + (3130134296413/2579800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2272051/2000000000000000000000 : ℝ)*base90 + (2272051/2000000000000000000000 : ℝ)*base92 + (2272051/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17923675421092944891411918501/3224750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (953580807/100000000000000 : ℝ)*(base19) + (869767559/100000000000000 : ℝ)*(base23) + (365729/3125000000000 : ℝ)*(upper2) + (79312047/100000000000000 : ℝ)*(upper3) + (162196907/100000000000000 : ℝ)*(upper5) + (1239638886698337/100000000000000 : ℝ)*(major0) + (1239638886698337/100000000000000 : ℝ)*(major1) + (1239638886698337/100000000000000 : ℝ)*(major2) + (455214543/10000000000000 : ℝ)*(sp1) + (2752413133/100000000000000 : ℝ)*(sp2) + (83669566223447/5000000000000 : ℝ)*(sp4) + (1673385818742703/100000000000000 : ℝ)*(sp5) + (209173462786031/12500000000000 : ℝ)*(sp6) + (402943131827869/50000000000000 : ℝ)*(sp7) + (402943131827869/50000000000000 : ℝ)*(f.failure) + (83669566223447/5000000000000 : ℝ)*(f.sum) + (257025137902147/128990000000000000000000000000 : ℝ)*base66 + (14170021989938118833/6449500000000000000000000000000000 : ℝ)*base67 + (19243283165489118833/6449500000000000000000000000000000 : ℝ)*base69 + (15971680914628118833/6449500000000000000000000000000000 : ℝ)*base71 + (218753352950003/128990000000000000000000000000 : ℝ)*base73 + (14094309370312381167/6449500000000000000000000000000000 : ℝ)*base76 + (15126125643003881167/6449500000000000000000000000000000 : ℝ)*base78 + (54679005138788618833/6449500000000000000000000000000000 : ℝ)*base79 + (52897054489153/128990000000000000000000000000 : ℝ)*base81 + (42624467/5000000000000000000000 : ℝ)*base90 + (42624467/5000000000000000000000 : ℝ)*base92 + (42624467/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1319_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13519/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (417/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19637/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1319_s2_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026578299/5000000000 : ℝ)*x 0 + (2743108607/5000000000 : ℝ)*x 1 + (258931273/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026578299/5000000000 : ℝ)^4279 ≤ (12477136271521/100000000000000 : ℝ)^3255 := by
    have hnat : (1026578299 : ℕ)^4279*100000000000000^3255 ≤ 12477136271521^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026578299 5000000000 12477136271521 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743108607/5000000000 : ℝ)^4279 ≤ (4542031335801/10000000000000 : ℝ)^3255 := by
    have hnat : (2743108607 : ℕ)^4279*10000000000000^3255 ≤ 4542031335801^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743108607 5000000000 4542031335801 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258931273/500000000 : ℝ)^4279 ≤ (42102550350187/100000000000000 : ℝ)^3255 := by
    have hnat : (258931273 : ℕ)^4279*100000000000000^3255 ≤ 42102550350187^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258931273 500000000 42102550350187 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026578299/5000000000 : ℝ), (2743108607/5000000000 : ℝ), (258931273/500000000 : ℝ)] ![(12477136271521/100000000000000 : ℝ), (4542031335801/10000000000000 : ℝ), (42102550350187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026578299/5000000000 : ℝ)|^4279 ≤ (12477136271521/100000000000000 : ℝ)^3255
        have hw : |(-1026578299/5000000000 : ℝ)|=(1026578299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743108607/5000000000 : ℝ)|^4279 ≤ (4542031335801/10000000000000 : ℝ)^3255
        have hw : |(2743108607/5000000000 : ℝ)|=(2743108607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258931273/500000000 : ℝ)|^4279 ≤ (42102550350187/100000000000000 : ℝ)^3255
        have hw : |(258931273/500000000 : ℝ)|=(258931273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367596519/10000000000 : ℝ)*x 0 + (-2212299111/10000000000 : ℝ)*x 1 + (41429/80000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367596519/10000000000 : ℝ)^4279 ≤ (22066859052957/50000000000000 : ℝ)^3255 := by
    have hnat : (5367596519 : ℕ)^4279*50000000000000^3255 ≤ 22066859052957^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367596519 10000000000 22066859052957 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212299111/10000000000 : ℝ)^4279 ≤ (13763736439553/100000000000000 : ℝ)^3255 := by
    have hnat : (2212299111 : ℕ)^4279*100000000000000^3255 ≤ 13763736439553^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212299111 10000000000 13763736439553 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41429/80000 : ℝ)^4279 ≤ (8420509086767/20000000000000 : ℝ)^3255 := by
    have hnat : (41429 : ℕ)^4279*20000000000000^3255 ≤ 8420509086767^3255*80000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41429 80000 8420509086767 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367596519/10000000000 : ℝ), (-2212299111/10000000000 : ℝ), (41429/80000 : ℝ)] ![(22066859052957/50000000000000 : ℝ), (13763736439553/100000000000000 : ℝ), (8420509086767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367596519/10000000000 : ℝ)|^4279 ≤ (22066859052957/50000000000000 : ℝ)^3255
        have hw : |(5367596519/10000000000 : ℝ)|=(5367596519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212299111/10000000000 : ℝ)|^4279 ≤ (13763736439553/100000000000000 : ℝ)^3255
        have hw : |(-2212299111/10000000000 : ℝ)|=(2212299111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41429/80000 : ℝ)|^4279 ≤ (8420509086767/20000000000000 : ℝ)^3255
        have hw : |(41429/80000 : ℝ)|=(41429/80000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367595857/10000000000 : ℝ)*x 0 + (103572513/200000000 : ℝ)*x 1 + (-2212299137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367595857/10000000000 : ℝ)^4279 ≤ (8826742190083/20000000000000 : ℝ)^3255 := by
    have hnat : (5367595857 : ℕ)^4279*20000000000000^3255 ≤ 8826742190083^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367595857 10000000000 8826742190083 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103572513/200000000 : ℝ)^4279 ≤ (8420510476171/20000000000000 : ℝ)^3255 := by
    have hnat : (103572513 : ℕ)^4279*20000000000000^3255 ≤ 8420510476171^3255*200000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103572513 200000000 8420510476171 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212299137/10000000000 : ℝ)^4279 ≤ (13763736652199/100000000000000 : ℝ)^3255 := by
    have hnat : (2212299137 : ℕ)^4279*100000000000000^3255 ≤ 13763736652199^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212299137 10000000000 13763736652199 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367595857/10000000000 : ℝ), (103572513/200000000 : ℝ), (-2212299137/10000000000 : ℝ)] ![(8826742190083/20000000000000 : ℝ), (8420510476171/20000000000000 : ℝ), (13763736652199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367595857/10000000000 : ℝ)|^4279 ≤ (8826742190083/20000000000000 : ℝ)^3255
        have hw : |(5367595857/10000000000 : ℝ)|=(5367595857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103572513/200000000 : ℝ)|^4279 ≤ (8420510476171/20000000000000 : ℝ)^3255
        have hw : |(103572513/200000000 : ℝ)|=(103572513/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2212299137/10000000000 : ℝ)|^4279 ≤ (13763736652199/100000000000000 : ℝ)^3255
        have hw : |(-2212299137/10000000000 : ℝ)|=(2212299137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162909447/5000000000 : ℝ)*x 0 + (1004390183/2500000000 : ℝ)*x 1 + (4656271431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162909447/5000000000 : ℝ)^4279 ≤ (1661682349169/5000000000000 : ℝ)^3255 := by
    have hnat : (2162909447 : ℕ)^4279*5000000000000^3255 ≤ 1661682349169^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162909447 5000000000 1661682349169 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004390183/2500000000 : ℝ)^4279 ≤ (3769483519943/12500000000000 : ℝ)^3255 := by
    have hnat : (1004390183 : ℕ)^4279*12500000000000^3255 ≤ 3769483519943^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004390183 2500000000 3769483519943 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4656271431/10000000000 : ℝ)^4279 ≤ (1830524241957/5000000000000 : ℝ)^3255 := by
    have hnat : (4656271431 : ℕ)^4279*5000000000000^3255 ≤ 1830524241957^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656271431 10000000000 1830524241957 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162909447/5000000000 : ℝ), (1004390183/2500000000 : ℝ), (4656271431/10000000000 : ℝ)] ![(1661682349169/5000000000000 : ℝ), (3769483519943/12500000000000 : ℝ), (1830524241957/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162909447/5000000000 : ℝ)|^4279 ≤ (1661682349169/5000000000000 : ℝ)^3255
        have hw : |(2162909447/5000000000 : ℝ)|=(2162909447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004390183/2500000000 : ℝ)|^4279 ≤ (3769483519943/12500000000000 : ℝ)^3255
        have hw : |(1004390183/2500000000 : ℝ)|=(1004390183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4656271431/10000000000 : ℝ)|^4279 ≤ (1830524241957/5000000000000 : ℝ)^3255
        have hw : |(4656271431/10000000000 : ℝ)|=(4656271431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-102661471/500000000 : ℝ)*x 0 + (5180604537/10000000000 : ℝ)*x 1 + (5484220053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102661471/500000000 : ℝ)^4279 ≤ (12477718038627/100000000000000 : ℝ)^3255 := by
    have hnat : (102661471 : ℕ)^4279*100000000000000^3255 ≤ 12477718038627^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102661471 500000000 12477718038627 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180604537/10000000000 : ℝ)^4279 ≤ (5265462931079/12500000000000 : ℝ)^3255 := by
    have hnat : (5180604537 : ℕ)^4279*12500000000000^3255 ≤ 5265462931079^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180604537 10000000000 5265462931079 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484220053/10000000000 : ℝ)^4279 ≤ (11349644627257/25000000000000 : ℝ)^3255 := by
    have hnat : (5484220053 : ℕ)^4279*25000000000000^3255 ≤ 11349644627257^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484220053 10000000000 11349644627257 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102661471/500000000 : ℝ), (5180604537/10000000000 : ℝ), (5484220053/10000000000 : ℝ)] ![(12477718038627/100000000000000 : ℝ), (5265462931079/12500000000000 : ℝ), (11349644627257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102661471/500000000 : ℝ)|^4279 ≤ (12477718038627/100000000000000 : ℝ)^3255
        have hw : |(-102661471/500000000 : ℝ)|=(102661471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180604537/10000000000 : ℝ)|^4279 ≤ (5265462931079/12500000000000 : ℝ)^3255
        have hw : |(5180604537/10000000000 : ℝ)|=(5180604537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484220053/10000000000 : ℝ)|^4279 ≤ (11349644627257/25000000000000 : ℝ)^3255
        have hw : |(5484220053/10000000000 : ℝ)|=(5484220053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288515619/10000000000 : ℝ)*x 0 + (-1906703583/10000000000 : ℝ)*x 1 + (137105503/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288515619/10000000000 : ℝ)^4279 ≤ (21640463649943/50000000000000 : ℝ)^3255 := by
    have hnat : (5288515619 : ℕ)^4279*50000000000000^3255 ≤ 21640463649943^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288515619 10000000000 21640463649943 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906703583/10000000000 : ℝ)^4279 ≤ (5660246721589/50000000000000 : ℝ)^3255 := by
    have hnat : (1906703583 : ℕ)^4279*50000000000000^3255 ≤ 5660246721589^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906703583 10000000000 5660246721589 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137105503/250000000 : ℝ)^4279 ≤ (45398579238139/100000000000000 : ℝ)^3255 := by
    have hnat : (137105503 : ℕ)^4279*100000000000000^3255 ≤ 45398579238139^3255*250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137105503 250000000 45398579238139 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288515619/10000000000 : ℝ), (-1906703583/10000000000 : ℝ), (137105503/250000000 : ℝ)] ![(21640463649943/50000000000000 : ℝ), (5660246721589/50000000000000 : ℝ), (45398579238139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288515619/10000000000 : ℝ)|^4279 ≤ (21640463649943/50000000000000 : ℝ)^3255
        have hw : |(5288515619/10000000000 : ℝ)|=(5288515619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906703583/10000000000 : ℝ)|^4279 ≤ (5660246721589/50000000000000 : ℝ)^3255
        have hw : |(-1906703583/10000000000 : ℝ)|=(1906703583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137105503/250000000 : ℝ)|^4279 ≤ (45398579238139/100000000000000 : ℝ)^3255
        have hw : |(137105503/250000000 : ℝ)|=(137105503/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41316529/78125000 : ℝ)*x 0 + (274211003/500000000 : ℝ)*x 1 + (-95335177/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41316529/78125000 : ℝ)^4279 ≤ (2705058018777/6250000000000 : ℝ)^3255 := by
    have hnat : (41316529 : ℕ)^4279*6250000000000^3255 ≤ 2705058018777^3255*78125000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41316529 78125000 2705058018777 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274211003/500000000 : ℝ)^4279 ≤ (11349644646301/25000000000000 : ℝ)^3255 := by
    have hnat : (274211003 : ℕ)^4279*25000000000000^3255 ≤ 11349644646301^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274211003 500000000 11349644646301 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95335177/500000000 : ℝ)^4279 ≤ (11320493107563/100000000000000 : ℝ)^3255 := by
    have hnat : (95335177 : ℕ)^4279*100000000000000^3255 ≤ 11320493107563^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95335177 500000000 11320493107563 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41316529/78125000 : ℝ), (274211003/500000000 : ℝ), (-95335177/500000000 : ℝ)] ![(2705058018777/6250000000000 : ℝ), (11349644646301/25000000000000 : ℝ), (11320493107563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41316529/78125000 : ℝ)|^4279 ≤ (2705058018777/6250000000000 : ℝ)^3255
        have hw : |(41316529/78125000 : ℝ)|=(41316529/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274211003/500000000 : ℝ)|^4279 ≤ (11349644646301/25000000000000 : ℝ)^3255
        have hw : |(274211003/500000000 : ℝ)|=(274211003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95335177/500000000 : ℝ)|^4279 ≤ (11320493107563/100000000000000 : ℝ)^3255
        have hw : |(-95335177/500000000 : ℝ)|=(95335177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s2_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21629843/50000000 : ℝ)*x 0 + (4652159787/10000000000 : ℝ)*x 1 + (2010856607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21629843/50000000 : ℝ)^4279 ≤ (664703179023/2000000000000 : ℝ)^3255 := by
    have hnat : (21629843 : ℕ)^4279*2000000000000^3255 ≤ 664703179023^3255*50000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21629843 50000000 664703179023 2000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4652159787/10000000000 : ℝ)^4279 ≤ (36567992205313/100000000000000 : ℝ)^3255 := by
    have hnat : (4652159787 : ℕ)^4279*100000000000000^3255 ≤ 36567992205313^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4652159787 10000000000 36567992205313 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010856607/5000000000 : ℝ)^4279 ≤ (15098424413251/50000000000000 : ℝ)^3255 := by
    have hnat : (2010856607 : ℕ)^4279*50000000000000^3255 ≤ 15098424413251^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010856607 5000000000 15098424413251 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21629843/50000000 : ℝ), (4652159787/10000000000 : ℝ), (2010856607/5000000000 : ℝ)] ![(664703179023/2000000000000 : ℝ), (36567992205313/100000000000000 : ℝ), (15098424413251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21629843/50000000 : ℝ)|^4279 ≤ (664703179023/2000000000000 : ℝ)^3255
        have hw : |(21629843/50000000 : ℝ)|=(21629843/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4652159787/10000000000 : ℝ)|^4279 ≤ (36567992205313/100000000000000 : ℝ)^3255
        have hw : |(4652159787/10000000000 : ℝ)|=(4652159787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2010856607/5000000000 : ℝ)|^4279 ≤ (15098424413251/50000000000000 : ℝ)^3255
        have hw : |(2010856607/5000000000 : ℝ)|=(2010856607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19637/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9697/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8099/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19637/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (417/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19637/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (417/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19637/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (417/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19637/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (417/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19637/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (417/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19637/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (417/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (417/6250 : ℝ) ^ (2139/512 : ℝ) ≤ (153096070980217/12500000000000000000 : ℝ) := by
    have hpowers : (417/6250 : ℝ)^2139 ≤ (153096070980217/12500000000000000000 : ℝ)^512 := by
      have hnat : (417 : ℕ)^2139*12500000000000000000^512 ≤ 153096070980217^512*6250^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        417 6250 153096070980217 12500000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (417/6250 : ℝ)) (X := (153096070980217/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19637/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (111341152485312103/100000000000000000000 : ℝ) := by
    have hpowers : (19637/100000 : ℝ)^2139 ≤ (111341152485312103/100000000000000000000 : ℝ)^512 := by
      have hnat : (19637 : ℕ)^2139*100000000000000000000^512 ≤ 111341152485312103^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19637 100000 111341152485312103 100000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19637/100000 : ℝ)) (X := (111341152485312103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250153096070980217/6250000000000000000 : ℝ) ≤ (500002931630037/500000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (6250153096070980217/6250000000000000000 : ℝ)^512 ≤ (500002931630037/500000000000000 : ℝ)^2139 := by
      have hnat : (6250153096070980217 : ℕ)^512*500000000000000^2139 ≤ 500002931630037^2139*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250153096070980217 6250000000000000000 500002931630037 500000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002931630037/500000000000000 : ℝ)) (X := (6250153096070980217/6250000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100112565921053153839/100000000000000000000 : ℝ) ≤ (1250336659036793/1250000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (100112565921053153839/100000000000000000000 : ℝ)^512 ≤ (1250336659036793/1250000000000000 : ℝ)^2139 := by
      have hnat : (100112565921053153839 : ℕ)^512*1250000000000000^2139 ≤ 1250336659036793^2139*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100112565921053153839 100000000000000000000 1250336659036793 1250000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250336659036793/1250000000000000 : ℝ)) (X := (100112565921053153839/100000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50111341152485312103/50000000000000000000 : ℝ) ≤ (2501331977996987/2500000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50111341152485312103/50000000000000000000 : ℝ)^512 ≤ (2501331977996987/2500000000000000 : ℝ)^2139 := by
      have hnat : (50111341152485312103 : ℕ)^512*2500000000000000^2139 ≤ 2501331977996987^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50111341152485312103 50000000000000000000 2501331977996987 2500000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501331977996987/2500000000000000 : ℝ)) (X := (50111341152485312103/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(153096070980217/12500000000000000000 : ℝ) ≤ ((32403900884899285581/32412500000000000000 : ℝ)+2*(658659923401/324125000000000 : ℝ)*(417/6250 : ℝ))^(2139/512 : ℝ) := by
    rw [show (32403900884899285581/32412500000000000000 : ℝ)+2*(658659923401/324125000000000 : ℝ)*(417/6250 : ℝ)=(500002931630037/500000000000000 : ℝ) by norm_num, show 1+2*(153096070980217/12500000000000000000 : ℝ)=(6250153096070980217/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(111341152485312103/100000000000000000000 : ℝ)+(153096070980217/12500000000000000000 : ℝ) ≤ ((32403900884899285581/32412500000000000000 : ℝ)+(658659923401/324125000000000 : ℝ)*((19637/100000 : ℝ)+(417/6250 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (32403900884899285581/32412500000000000000 : ℝ)+(658659923401/324125000000000 : ℝ)*((19637/100000 : ℝ)+(417/6250 : ℝ))=(1250336659036793/1250000000000000 : ℝ) by norm_num, show 1+(111341152485312103/100000000000000000000 : ℝ)+(153096070980217/12500000000000000000 : ℝ)=(100112565921053153839/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(111341152485312103/100000000000000000000 : ℝ) ≤ ((32403900884899285581/32412500000000000000 : ℝ)+2*(658659923401/324125000000000 : ℝ)*(19637/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (32403900884899285581/32412500000000000000 : ℝ)+2*(658659923401/324125000000000 : ℝ)*(19637/100000 : ℝ)=(2501331977996987/2500000000000000 : ℝ) by norm_num, show 1+2*(111341152485312103/100000000000000000000 : ℝ)=(50111341152485312103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32403900884899285581/32412500000000000000 : ℝ)*(X 1 0+X 2 0)+(658659923401/324125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (417/6250 : ℝ)) (hi := (19637/100000 : ℝ)) (c := (32403900884899285581/32412500000000000000 : ℝ)) (alpha := (658659923401/324125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32403900884899285581/32412500000000000000 : ℝ)*(X 0 1+X 2 1)+(658659923401/324125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (417/6250 : ℝ)) (hi := (19637/100000 : ℝ)) (c := (32403900884899285581/32412500000000000000 : ℝ)) (alpha := (658659923401/324125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32403900884899285581/32412500000000000000 : ℝ)*(X 0 2+X 1 2)+(658659923401/324125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (417/6250 : ℝ)) (hi := (19637/100000 : ℝ)) (c := (32403900884899285581/32412500000000000000 : ℝ)) (alpha := (658659923401/324125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1026578299/5000000000 : ℝ)*X 0 0+(2743108607/5000000000 : ℝ)*X 0 1+(258931273/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5367596519/10000000000 : ℝ)*X 1 0+(-2212299111/10000000000 : ℝ)*X 1 1+(41429/80000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367595857/10000000000 : ℝ)*X 2 0+(103572513/200000000 : ℝ)*X 2 1+(-2212299137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162909447/5000000000 : ℝ)*X 0 0+(1004390183/2500000000 : ℝ)*X 0 1+(4656271431/10000000000 : ℝ)*X 0 2+(2162909447/5000000000 : ℝ)*X 1 0+(1004390183/2500000000 : ℝ)*X 1 1+(4656271431/10000000000 : ℝ)*X 1 2+(2162909447/5000000000 : ℝ)*X 2 0+(1004390183/2500000000 : ℝ)*X 2 1+(4656271431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-102661471/500000000 : ℝ)*X 0 0+(5180604537/10000000000 : ℝ)*X 0 1+(5484220053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288515619/10000000000 : ℝ)*X 1 0+(-1906703583/10000000000 : ℝ)*X 1 1+(137105503/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41316529/78125000 : ℝ)*X 2 0+(274211003/500000000 : ℝ)*X 2 1+(-95335177/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((21629843/50000000 : ℝ)*X 0 0+(4652159787/10000000000 : ℝ)*X 0 1+(2010856607/5000000000 : ℝ)*X 0 2+(21629843/50000000 : ℝ)*X 1 0+(4652159787/10000000000 : ℝ)*X 1 1+(2010856607/5000000000 : ℝ)*X 1 2+(21629843/50000000 : ℝ)*X 2 0+(4652159787/10000000000 : ℝ)*X 2 1+(2010856607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1459990616765368979590315851/405156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (868377967/50000000000000 : ℝ)*(base19) + (39472597/5000000000000 : ℝ)*(base23) + (29325349/10000000000000 : ℝ)*(lower2) + (657703453/100000000000000 : ℝ)*(upper3) + (10537229/10000000000000 : ℝ)*(upper5) + (1204188724454443/50000000000000 : ℝ)*(major0) + (1204188724454443/50000000000000 : ℝ)*(major1) + (1204188724454443/50000000000000 : ℝ)*(major2) + (325107339605437/10000000000000 : ℝ)*(sp0) + (1625536322169229/50000000000000 : ℝ)*(sp1) + (812768397910613/25000000000000 : ℝ)*(sp2) + (1565664509220513/100000000000000 : ℝ)*(sp3) + (985040023/100000000000000 : ℝ)*(sp4) + (3177477073/20000000000000 : ℝ)*(sp7) + (782840198302939/50000000000000 : ℝ)*(f.failure) + (406384297636799/12500000000000 : ℝ)*(f.sum) + (62630371316497/32412500000000000000000000000 : ℝ)*base65 + (2560438293566836383/1620625000000000000000000000000000 : ℝ)*base67 + (12478955758739413617/1620625000000000000000000000000000 : ℝ)*base70 + (11398165019788086383/1620625000000000000000000000000000 : ℝ)*base71 + (222363334841581/64825000000000000000000000000 : ℝ)*base74 + (10388373209677461383/1620625000000000000000000000000000 : ℝ)*base75 + (6598046103809336383/1620625000000000000000000000000000 : ℝ)*base77 + (17305234162618711383/1620625000000000000000000000000000 : ℝ)*base79 + (310078778494281/64825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (10935477/5000000000000000000000 : ℝ)*base90 + (10935477/5000000000000000000000 : ℝ)*base92 + (10935477/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1933941580835295340268043987/810312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106300611/20000000000000 : ℝ)*(base19) + (72903751/10000000000000 : ℝ)*(base23) + (22242149/25000000000000 : ℝ)*(upper3) + (1233011/2500000000000 : ℝ)*(lower4) + (1219953862624391/50000000000000 : ℝ)*(major0) + (1219953862624391/50000000000000 : ℝ)*(major1) + (1219953862624391/50000000000000 : ℝ)*(major2) + (1416202707/25000000000000 : ℝ)*(sp1) + (350596117/4000000000000 : ℝ)*(sp2) + (4746957/5000000000000 : ℝ)*(sp3) + (3293637217397361/100000000000000 : ℝ)*(sp4) + (1646815510541739/50000000000000 : ℝ)*(sp5) + (1646813861728463/50000000000000 : ℝ)*(sp6) + (1586178058605671/100000000000000 : ℝ)*(sp7) + (158617815354481/10000000000000 : ℝ)*(f.failure) + (3293637217397361/100000000000000 : ℝ)*(f.sum) + (58062083927543/16206250000000000000000000000 : ℝ)*base66 + (3711042896960556171/1620625000000000000000000000000000 : ℝ)*base67 + (4518443696192431171/1620625000000000000000000000000000 : ℝ)*base69 + (6853427325089443829/1620625000000000000000000000000000 : ℝ)*base72 + (51609961964047/64825000000000000000000000000 : ℝ)*base74 + (19536455940185556171/1620625000000000000000000000000000 : ℝ)*base75 + (4375900783113818829/1620625000000000000000000000000000 : ℝ)*base78 + (20643762438754931171/1620625000000000000000000000000000 : ℝ)*base79 + (190064830165097/64825000000000000000000000000 : ℝ)*base82 + (13931583/1000000000000000000000 : ℝ)*base90 + (13931583/1000000000000000000000 : ℝ)*base92 + (13931583/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1319_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19637/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1319_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1319_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1319_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1319_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1319_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

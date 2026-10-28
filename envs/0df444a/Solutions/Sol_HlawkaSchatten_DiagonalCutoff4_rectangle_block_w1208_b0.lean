-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1208_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:05:41.453356+00:00
-- url     : https://prove2.me/submissions/88bf7f31-578d-41b5-bd07-e94d1cbe134d

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
theorem support_rectangle_w1208_s0_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871096441/10000000000 : ℝ)*x 0 + (1509800303/2500000000 : ℝ)*x 1 + (4788762401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871096441/10000000000 : ℝ)^8401 ≤ (5450216113027/50000000000000 : ℝ)^6353 := by
    have hnat : (1871096441 : ℕ)^8401*50000000000000^6353 ≤ 5450216113027^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871096441 10000000000 5450216113027 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1509800303/2500000000 : ℝ)^8401 ≤ (51330374568967/100000000000000 : ℝ)^6353 := by
    have hnat : (1509800303 : ℕ)^8401*100000000000000^6353 ≤ 51330374568967^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509800303 2500000000 51330374568967 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4788762401/10000000000 : ℝ)^8401 ≤ (37769193179563/100000000000000 : ℝ)^6353 := by
    have hnat : (4788762401 : ℕ)^8401*100000000000000^6353 ≤ 37769193179563^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788762401 10000000000 37769193179563 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871096441/10000000000 : ℝ), (1509800303/2500000000 : ℝ), (4788762401/10000000000 : ℝ)] ![(5450216113027/50000000000000 : ℝ), (51330374568967/100000000000000 : ℝ), (37769193179563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871096441/10000000000 : ℝ)|^8401 ≤ (5450216113027/50000000000000 : ℝ)^6353
        have hw : |(-1871096441/10000000000 : ℝ)|=(1871096441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1509800303/2500000000 : ℝ)|^8401 ≤ (51330374568967/100000000000000 : ℝ)^6353
        have hw : |(1509800303/2500000000 : ℝ)|=(1509800303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4788762401/10000000000 : ℝ)|^8401 ≤ (37769193179563/100000000000000 : ℝ)^6353
        have hw : |(4788762401/10000000000 : ℝ)|=(4788762401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2756537531/5000000000 : ℝ)*x 0 + (-1293435371/5000000000 : ℝ)*x 1 + (2394381191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756537531/5000000000 : ℝ)^8401 ≤ (22750855881741/50000000000000 : ℝ)^6353 := by
    have hnat : (2756537531 : ℕ)^8401*50000000000000^6353 ≤ 22750855881741^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756537531 5000000000 22750855881741 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293435371/5000000000 : ℝ)^8401 ≤ (16729095236787/100000000000000 : ℝ)^6353 := by
    have hnat : (1293435371 : ℕ)^8401*100000000000000^6353 ≤ 16729095236787^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293435371 5000000000 16729095236787 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394381191/5000000000 : ℝ)^8401 ≤ (37769192981401/100000000000000 : ℝ)^6353 := by
    have hnat : (2394381191 : ℕ)^8401*100000000000000^6353 ≤ 37769192981401^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394381191 5000000000 37769192981401 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756537531/5000000000 : ℝ), (-1293435371/5000000000 : ℝ), (2394381191/5000000000 : ℝ)] ![(22750855881741/50000000000000 : ℝ), (16729095236787/100000000000000 : ℝ), (37769192981401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756537531/5000000000 : ℝ)|^8401 ≤ (22750855881741/50000000000000 : ℝ)^6353
        have hw : |(2756537531/5000000000 : ℝ)|=(2756537531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1293435371/5000000000 : ℝ)|^8401 ≤ (16729095236787/100000000000000 : ℝ)^6353
        have hw : |(-1293435371/5000000000 : ℝ)|=(1293435371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2394381191/5000000000 : ℝ)|^8401 ≤ (37769192981401/100000000000000 : ℝ)^6353
        have hw : |(2394381191/5000000000 : ℝ)|=(2394381191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689134381/1250000000 : ℝ)*x 0 + (1197190599/2500000000 : ℝ)*x 1 + (-2586870743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689134381/1250000000 : ℝ)^8401 ≤ (22750855805343/50000000000000 : ℝ)^6353 := by
    have hnat : (689134381 : ℕ)^8401*50000000000000^6353 ≤ 22750855805343^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689134381 1250000000 22750855805343 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1197190599/2500000000 : ℝ)^8401 ≤ (7553838625483/20000000000000 : ℝ)^6353 := by
    have hnat : (1197190599 : ℕ)^8401*20000000000000^6353 ≤ 7553838625483^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197190599 2500000000 7553838625483 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586870743/10000000000 : ℝ)^8401 ≤ (16729095245339/100000000000000 : ℝ)^6353 := by
    have hnat : (2586870743 : ℕ)^8401*100000000000000^6353 ≤ 16729095245339^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586870743 10000000000 16729095245339 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689134381/1250000000 : ℝ), (1197190599/2500000000 : ℝ), (-2586870743/10000000000 : ℝ)] ![(22750855805343/50000000000000 : ℝ), (7553838625483/20000000000000 : ℝ), (16729095245339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689134381/1250000000 : ℝ)|^8401 ≤ (22750855805343/50000000000000 : ℝ)^6353
        have hw : |(689134381/1250000000 : ℝ)|=(689134381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1197190599/2500000000 : ℝ)|^8401 ≤ (7553838625483/20000000000000 : ℝ)^6353
        have hw : |(1197190599/2500000000 : ℝ)|=(1197190599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2586870743/10000000000 : ℝ)|^8401 ≤ (16729095245339/100000000000000 : ℝ)^6353
        have hw : |(-2586870743/10000000000 : ℝ)|=(2586870743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048926259/2500000000 : ℝ)*x 0 + (1559108173/5000000000 : ℝ)*x 1 + (5638177293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048926259/2500000000 : ℝ)^8401 ≤ (31710972915109/100000000000000 : ℝ)^6353 := by
    have hnat : (1048926259 : ℕ)^8401*100000000000000^6353 ≤ 31710972915109^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048926259 2500000000 31710972915109 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559108173/5000000000 : ℝ)^8401 ≤ (4283394932057/20000000000000 : ℝ)^6353 := by
    have hnat : (1559108173 : ℕ)^8401*20000000000000^6353 ≤ 4283394932057^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559108173 5000000000 4283394932057 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5638177293/10000000000 : ℝ)^8401 ≤ (4687205241303/10000000000000 : ℝ)^6353 := by
    have hnat : (5638177293 : ℕ)^8401*10000000000000^6353 ≤ 4687205241303^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638177293 10000000000 4687205241303 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048926259/2500000000 : ℝ), (1559108173/5000000000 : ℝ), (5638177293/10000000000 : ℝ)] ![(31710972915109/100000000000000 : ℝ), (4283394932057/20000000000000 : ℝ), (4687205241303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048926259/2500000000 : ℝ)|^8401 ≤ (31710972915109/100000000000000 : ℝ)^6353
        have hw : |(1048926259/2500000000 : ℝ)|=(1048926259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559108173/5000000000 : ℝ)|^8401 ≤ (4283394932057/20000000000000 : ℝ)^6353
        have hw : |(1559108173/5000000000 : ℝ)|=(1559108173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5638177293/10000000000 : ℝ)|^8401 ≤ (4687205241303/10000000000000 : ℝ)^6353
        have hw : |(5638177293/10000000000 : ℝ)|=(5638177293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876051109/10000000000 : ℝ)*x 0 + (1205246279/2500000000 : ℝ)*x 1 + (600584093/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876051109/10000000000 : ℝ)^8401 ≤ (1367327226373/12500000000000 : ℝ)^6353 := by
    have hnat : (1876051109 : ℕ)^8401*12500000000000^6353 ≤ 1367327226373^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876051109 10000000000 1367327226373 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205246279/2500000000 : ℝ)^8401 ≤ (19052813146389/50000000000000 : ℝ)^6353 := by
    have hnat : (1205246279 : ℕ)^8401*50000000000000^6353 ≤ 19052813146389^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205246279 2500000000 19052813146389 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600584093/1000000000 : ℝ)^8401 ≤ (25477877941297/50000000000000 : ℝ)^6353 := by
    have hnat : (600584093 : ℕ)^8401*50000000000000^6353 ≤ 25477877941297^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600584093 1000000000 25477877941297 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876051109/10000000000 : ℝ), (1205246279/2500000000 : ℝ), (600584093/1000000000 : ℝ)] ![(1367327226373/12500000000000 : ℝ), (19052813146389/50000000000000 : ℝ), (25477877941297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876051109/10000000000 : ℝ)|^8401 ≤ (1367327226373/12500000000000 : ℝ)^6353
        have hw : |(-1876051109/10000000000 : ℝ)|=(1876051109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1205246279/2500000000 : ℝ)|^8401 ≤ (19052813146389/50000000000000 : ℝ)^6353
        have hw : |(1205246279/2500000000 : ℝ)|=(1205246279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600584093/1000000000 : ℝ)|^8401 ≤ (25477877941297/50000000000000 : ℝ)^6353
        have hw : |(600584093/1000000000 : ℝ)|=(600584093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172996459/10000000000 : ℝ)*x 0 + (-136979069/1000000000 : ℝ)*x 1 + (600584257/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172996459/10000000000 : ℝ)^8401 ≤ (20913754266553/50000000000000 : ℝ)^6353 := by
    have hnat : (5172996459 : ℕ)^8401*50000000000000^6353 ≤ 20913754266553^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172996459 10000000000 20913754266553 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136979069/1000000000 : ℝ)^8401 ≤ (1804179291933/25000000000000 : ℝ)^6353 := by
    have hnat : (136979069 : ℕ)^8401*25000000000000^6353 ≤ 1804179291933^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136979069 1000000000 1804179291933 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600584257/1000000000 : ℝ)^8401 ≤ (12738943570623/25000000000000 : ℝ)^6353 := by
    have hnat : (600584257 : ℕ)^8401*25000000000000^6353 ≤ 12738943570623^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600584257 1000000000 12738943570623 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172996459/10000000000 : ℝ), (-136979069/1000000000 : ℝ), (600584257/1000000000 : ℝ)] ![(20913754266553/50000000000000 : ℝ), (1804179291933/25000000000000 : ℝ), (12738943570623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172996459/10000000000 : ℝ)|^8401 ≤ (20913754266553/50000000000000 : ℝ)^6353
        have hw : |(5172996459/10000000000 : ℝ)|=(5172996459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136979069/1000000000 : ℝ)|^8401 ≤ (1804179291933/25000000000000 : ℝ)^6353
        have hw : |(-136979069/1000000000 : ℝ)|=(136979069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600584257/1000000000 : ℝ)|^8401 ≤ (12738943570623/25000000000000 : ℝ)^6353
        have hw : |(600584257/1000000000 : ℝ)|=(600584257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586498633/5000000000 : ℝ)*x 0 + (1501460357/2500000000 : ℝ)*x 1 + (-342447823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586498633/5000000000 : ℝ)^8401 ≤ (41827517161809/100000000000000 : ℝ)^6353 := by
    have hnat : (2586498633 : ℕ)^8401*100000000000000^6353 ≤ 41827517161809^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586498633 5000000000 41827517161809 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501460357/2500000000 : ℝ)^8401 ≤ (1273894036747/2500000000000 : ℝ)^6353 := by
    have hnat : (1501460357 : ℕ)^8401*2500000000000^6353 ≤ 1273894036747^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501460357 2500000000 1273894036747 2500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342447823/2500000000 : ℝ)^8401 ≤ (7216721361787/100000000000000 : ℝ)^6353 := by
    have hnat : (342447823 : ℕ)^8401*100000000000000^6353 ≤ 7216721361787^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342447823 2500000000 7216721361787 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586498633/5000000000 : ℝ), (1501460357/2500000000 : ℝ), (-342447823/2500000000 : ℝ)] ![(41827517161809/100000000000000 : ℝ), (1273894036747/2500000000000 : ℝ), (7216721361787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586498633/5000000000 : ℝ)|^8401 ≤ (41827517161809/100000000000000 : ℝ)^6353
        have hw : |(2586498633/5000000000 : ℝ)|=(2586498633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1501460357/2500000000 : ℝ)|^8401 ≤ (1273894036747/2500000000000 : ℝ)^6353
        have hw : |(1501460357/2500000000 : ℝ)|=(1501460357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342447823/2500000000 : ℝ)|^8401 ≤ (7216721361787/100000000000000 : ℝ)^6353
        have hw : |(-342447823/2500000000 : ℝ)|=(342447823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s0_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2102844477/5000000000 : ℝ)*x 0 + (5573243737/10000000000 : ℝ)*x 1 + (1592720797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102844477/5000000000 : ℝ)^8401 ≤ (7952698610167/25000000000000 : ℝ)^6353 := by
    have hnat : (2102844477 : ℕ)^8401*25000000000000^6353 ≤ 7952698610167^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102844477 5000000000 7952698610167 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5573243737/10000000000 : ℝ)^8401 ≤ (11539887019409/25000000000000 : ℝ)^6353 := by
    have hnat : (5573243737 : ℕ)^8401*25000000000000^6353 ≤ 11539887019409^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573243737 10000000000 11539887019409 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592720797/5000000000 : ℝ)^8401 ≤ (4405931493719/20000000000000 : ℝ)^6353 := by
    have hnat : (1592720797 : ℕ)^8401*20000000000000^6353 ≤ 4405931493719^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592720797 5000000000 4405931493719 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102844477/5000000000 : ℝ), (5573243737/10000000000 : ℝ), (1592720797/5000000000 : ℝ)] ![(7952698610167/25000000000000 : ℝ), (11539887019409/25000000000000 : ℝ), (4405931493719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102844477/5000000000 : ℝ)|^8401 ≤ (7952698610167/25000000000000 : ℝ)^6353
        have hw : |(2102844477/5000000000 : ℝ)|=(2102844477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5573243737/10000000000 : ℝ)|^8401 ≤ (11539887019409/25000000000000 : ℝ)^6353
        have hw : |(5573243737/10000000000 : ℝ)|=(5573243737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592720797/5000000000 : ℝ)|^8401 ≤ (4405931493719/20000000000000 : ℝ)^6353
        have hw : |(1592720797/5000000000 : ℝ)|=(1592720797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (341/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6891/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (525/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^525 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^525*1^128 ≤ 0^128*1^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (525/128 : ℝ) ≤ (2332513592207850343/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^525 ≤ (2332513592207850343/100000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^525*100000000000000000000^128 ≤ 2332513592207850343^128*5^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2332513592207850343 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2332513592207850343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^525 := by
      have hnat : (1 : ℕ)^128*1^525 ≤ 1^525*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (102332513592207850343/100000000000000000000 : ℝ) ≤ (10056374108983843/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (102332513592207850343/100000000000000000000 : ℝ)^128 ≤ (10056374108983843/10000000000000000 : ℝ)^525 := by
      have hnat : (102332513592207850343 : ℕ)^128*10000000000000000^525 ≤ 10056374108983843^525*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102332513592207850343 100000000000000000000 10056374108983843 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056374108983843/10000000000000000 : ℝ)) (X := (102332513592207850343/100000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (52332513592207850343/50000000000000000000 : ℝ) ≤ (5056374108983843/5000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (52332513592207850343/50000000000000000000 : ℝ)^128 ≤ (5056374108983843/5000000000000000 : ℝ)^525 := by
      have hnat : (52332513592207850343 : ℕ)^128*5000000000000000^525 ≤ 5056374108983843^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52332513592207850343 50000000000000000000 5056374108983843 5000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056374108983843/5000000000000000 : ℝ)) (X := (52332513592207850343/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56374108983843/4000000000000000 : ℝ)*(0 : ℝ))^(525/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(56374108983843/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2332513592207850343/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56374108983843/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(525/128 : ℝ) := by
    rw [show (1 : ℝ)+(56374108983843/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056374108983843/10000000000000000 : ℝ) by norm_num, show 1+(2332513592207850343/100000000000000000000 : ℝ)+(0 : ℝ)=(102332513592207850343/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2332513592207850343/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56374108983843/4000000000000000 : ℝ)*(2/5 : ℝ))^(525/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(56374108983843/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056374108983843/5000000000000000 : ℝ) by norm_num, show 1+2*(2332513592207850343/100000000000000000000 : ℝ)=(52332513592207850343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56374108983843/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56374108983843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56374108983843/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56374108983843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56374108983843/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56374108983843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1871096441/10000000000 : ℝ)*X 0 0+(1509800303/2500000000 : ℝ)*X 0 1+(4788762401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2756537531/5000000000 : ℝ)*X 1 0+(-1293435371/5000000000 : ℝ)*X 1 1+(2394381191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689134381/1250000000 : ℝ)*X 2 0+(1197190599/2500000000 : ℝ)*X 2 1+(-2586870743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048926259/2500000000 : ℝ)*X 0 0+(1559108173/5000000000 : ℝ)*X 0 1+(5638177293/10000000000 : ℝ)*X 0 2+(1048926259/2500000000 : ℝ)*X 1 0+(1559108173/5000000000 : ℝ)*X 1 1+(5638177293/10000000000 : ℝ)*X 1 2+(1048926259/2500000000 : ℝ)*X 2 0+(1559108173/5000000000 : ℝ)*X 2 1+(5638177293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1876051109/10000000000 : ℝ)*X 0 0+(1205246279/2500000000 : ℝ)*X 0 1+(600584093/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172996459/10000000000 : ℝ)*X 1 0+(-136979069/1000000000 : ℝ)*X 1 1+(600584257/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586498633/5000000000 : ℝ)*X 2 0+(1501460357/2500000000 : ℝ)*X 2 1+(-342447823/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102844477/5000000000 : ℝ)*X 0 0+(5573243737/10000000000 : ℝ)*X 0 1+(1592720797/5000000000 : ℝ)*X 0 2+(2102844477/5000000000 : ℝ)*X 1 0+(5573243737/10000000000 : ℝ)*X 1 1+(1592720797/5000000000 : ℝ)*X 1 2+(2102844477/5000000000 : ℝ)*X 2 0+(5573243737/10000000000 : ℝ)*X 2 1+(1592720797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (530409034751490333505959/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58309007/100000000000000 : ℝ)*(base1) + (649371037/50000000000000 : ℝ)*(base19) + (241561943/20000000000000 : ℝ)*(base23) + (88901523/100000000000000 : ℝ)*(base24) + (928891/312500000000 : ℝ)*(upper3) + (299140463076443/50000000000000 : ℝ)*(major0) + (299140463076443/50000000000000 : ℝ)*(major1) + (299140463076443/50000000000000 : ℝ)*(major2) + (799723651998177/100000000000000 : ℝ)*(sp0) + (399862585827561/50000000000000 : ℝ)*(sp1) + (399862586842979/50000000000000 : ℝ)*(sp2) + (198416437472719/50000000000000 : ℝ)*(sp3) + (1438354013/50000000000000 : ℝ)*(sp4) + (2271851117/100000000000000 : ℝ)*(sp7) + (198417602552781/50000000000000 : ℝ)*(f.failure) + (199931617599299/25000000000000 : ℝ)*(f.sum) + (23392511410449/100000000000000000000000000000 : ℝ)*base65 + (454479297510449/200000000000000000000000000000 : ℝ)*base67 + (411677036889551/200000000000000000000000000000 : ℝ)*base70 + (119741370910449/200000000000000000000000000000 : ℝ)*base71 + (157533035610449/100000000000000000000000000000 : ℝ)*base73 + (355768273710449/200000000000000000000000000000 : ℝ)*base75 + (344739686910449/200000000000000000000000000000 : ℝ)*base77 + (214538531910449/200000000000000000000000000000 : ℝ)*base79 + (578704942889551/100000000000000000000000000000 : ℝ)*base82 + (7060673/5000000000000000000000 : ℝ)*base90 + (7060673/5000000000000000000000 : ℝ)*base92 + (7060673/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96938337899953523436471/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52798727/4000000000000 : ℝ)*(base19) + (304688249/20000000000000 : ℝ)*(base23) + (56595919/100000000000000 : ℝ)*(base39) + (142835011/50000000000000 : ℝ)*(upper3) + (836573/1250000000000 : ℝ)*(upper5) + (315694713209319/50000000000000 : ℝ)*(major0) + (315694713209319/50000000000000 : ℝ)*(major1) + (631389369822719/100000000000000 : ℝ)*(major2) + (624378299/20000000000000 : ℝ)*(sp1) + (1688388593/50000000000000 : ℝ)*(sp2) + (421991406105387/50000000000000 : ℝ)*(sp4) + (51512351706/6103515625 : ℝ)*(sp5) + (421988984294131/50000000000000 : ℝ)*(sp6) + (209397911233339/50000000000000 : ℝ)*(sp7) + (209397911233339/50000000000000 : ℝ)*(f.failure) + (210995717201673/25000000000000 : ℝ)*(f.sum) + (224475537005049/400000000000000000000000000000 : ℝ)*base66 + (3511880042670883/400000000000000000000000000000 : ℝ)*base68 + (2001636462367083/200000000000000000000000000000 : ℝ)*base70 + (2738791149870883/400000000000000000000000000000 : ℝ)*base72 + (1527238813005049/400000000000000000000000000000 : ℝ)*base74 + (1584688172367083/200000000000000000000000000000 : ℝ)*base76 + (1329483838367083/200000000000000000000000000000 : ℝ)*base78 + (1517621847567083/200000000000000000000000000000 : ℝ)*base80 + (476951654967083/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (40290713/5000000000000000000000 : ℝ)*base89 + (40290713/5000000000000000000000 : ℝ)*base91 + (40290713/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1208_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6891/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1208_s1_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070979287/10000000000 : ℝ)*x 0 + (284211459/500000000 : ℝ)*x 1 + (156743293/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070979287/10000000000 : ℝ)^8401 ≤ (498646887687/4000000000000 : ℝ)^6353 := by
    have hnat : (2070979287 : ℕ)^8401*4000000000000^6353 ≤ 498646887687^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070979287 10000000000 498646887687 4000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284211459/500000000 : ℝ)^8401 ≤ (11844744769631/25000000000000 : ℝ)^6353 := by
    have hnat : (284211459 : ℕ)^8401*25000000000000^6353 ≤ 11844744769631^6353*500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284211459 500000000 11844744769631 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156743293/312500000 : ℝ)^8401 ≤ (2007742435713/5000000000000 : ℝ)^6353 := by
    have hnat : (156743293 : ℕ)^8401*5000000000000^6353 ≤ 2007742435713^6353*312500000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156743293 312500000 2007742435713 5000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070979287/10000000000 : ℝ), (284211459/500000000 : ℝ), (156743293/312500000 : ℝ)] ![(498646887687/4000000000000 : ℝ), (11844744769631/25000000000000 : ℝ), (2007742435713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070979287/10000000000 : ℝ)|^8401 ≤ (498646887687/4000000000000 : ℝ)^6353
        have hw : |(-2070979287/10000000000 : ℝ)|=(2070979287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284211459/500000000 : ℝ)|^8401 ≤ (11844744769631/25000000000000 : ℝ)^6353
        have hw : |(284211459/500000000 : ℝ)|=(284211459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156743293/312500000 : ℝ)|^8401 ≤ (2007742435713/5000000000000 : ℝ)^6353
        have hw : |(156743293/312500000 : ℝ)|=(156743293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5415509367/10000000000 : ℝ)*x 0 + (-2430517031/10000000000 : ℝ)*x 1 + (5015785849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415509367/10000000000 : ℝ)^8401 ≤ (22219962256207/50000000000000 : ℝ)^6353 := by
    have hnat : (5415509367 : ℕ)^8401*50000000000000^6353 ≤ 22219962256207^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415509367 10000000000 22219962256207 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2430517031/10000000000 : ℝ)^8401 ≤ (15405221762167/100000000000000 : ℝ)^6353 := by
    have hnat : (2430517031 : ℕ)^8401*100000000000000^6353 ≤ 15405221762167^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430517031 10000000000 15405221762167 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015785849/10000000000 : ℝ)^8401 ≤ (2007742686083/5000000000000 : ℝ)^6353 := by
    have hnat : (5015785849 : ℕ)^8401*5000000000000^6353 ≤ 2007742686083^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015785849 10000000000 2007742686083 5000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415509367/10000000000 : ℝ), (-2430517031/10000000000 : ℝ), (5015785849/10000000000 : ℝ)] ![(22219962256207/50000000000000 : ℝ), (15405221762167/100000000000000 : ℝ), (2007742686083/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415509367/10000000000 : ℝ)|^8401 ≤ (22219962256207/50000000000000 : ℝ)^6353
        have hw : |(5415509367/10000000000 : ℝ)|=(5415509367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2430517031/10000000000 : ℝ)|^8401 ≤ (15405221762167/100000000000000 : ℝ)^6353
        have hw : |(-2430517031/10000000000 : ℝ)|=(2430517031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015785849/10000000000 : ℝ)|^8401 ≤ (2007742686083/5000000000000 : ℝ)^6353
        have hw : |(5015785849/10000000000 : ℝ)|=(5015785849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2707754053/5000000000 : ℝ)*x 0 + (2507893327/5000000000 : ℝ)*x 1 + (-1215258823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707754053/5000000000 : ℝ)^8401 ≤ (11109977707197/25000000000000 : ℝ)^6353 := by
    have hnat : (2707754053 : ℕ)^8401*25000000000000^6353 ≤ 11109977707197^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707754053 5000000000 11109977707197 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507893327/5000000000 : ℝ)^8401 ≤ (40154862243769/100000000000000 : ℝ)^6353 := by
    have hnat : (2507893327 : ℕ)^8401*100000000000000^6353 ≤ 40154862243769^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507893327 5000000000 40154862243769 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215258823/5000000000 : ℝ)^8401 ≤ (7702613458393/50000000000000 : ℝ)^6353 := by
    have hnat : (1215258823 : ℕ)^8401*50000000000000^6353 ≤ 7702613458393^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215258823 5000000000 7702613458393 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707754053/5000000000 : ℝ), (2507893327/5000000000 : ℝ), (-1215258823/5000000000 : ℝ)] ![(11109977707197/25000000000000 : ℝ), (40154862243769/100000000000000 : ℝ), (7702613458393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707754053/5000000000 : ℝ)|^8401 ≤ (11109977707197/25000000000000 : ℝ)^6353
        have hw : |(2707754053/5000000000 : ℝ)|=(2707754053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507893327/5000000000 : ℝ)|^8401 ≤ (40154862243769/100000000000000 : ℝ)^6353
        have hw : |(2507893327/5000000000 : ℝ)|=(2507893327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1215258823/5000000000 : ℝ)|^8401 ≤ (7702613458393/50000000000000 : ℝ)^6353
        have hw : |(-1215258823/5000000000 : ℝ)|=(1215258823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155898233/5000000000 : ℝ)*x 0 + (3689272683/10000000000 : ℝ)*x 1 + (1007272509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155898233/5000000000 : ℝ)^8401 ≤ (32876379743853/100000000000000 : ℝ)^6353 := by
    have hnat : (2155898233 : ℕ)^8401*100000000000000^6353 ≤ 32876379743853^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155898233 5000000000 32876379743853 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3689272683/10000000000 : ℝ)^8401 ≤ (5350157604583/20000000000000 : ℝ)^6353 := by
    have hnat : (3689272683 : ℕ)^8401*20000000000000^6353 ≤ 5350157604583^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689272683 10000000000 5350157604583 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007272509/2000000000 : ℝ)^8401 ≤ (40372832214121/100000000000000 : ℝ)^6353 := by
    have hnat : (1007272509 : ℕ)^8401*100000000000000^6353 ≤ 40372832214121^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007272509 2000000000 40372832214121 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155898233/5000000000 : ℝ), (3689272683/10000000000 : ℝ), (1007272509/2000000000 : ℝ)] ![(32876379743853/100000000000000 : ℝ), (5350157604583/20000000000000 : ℝ), (40372832214121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155898233/5000000000 : ℝ)|^8401 ≤ (32876379743853/100000000000000 : ℝ)^6353
        have hw : |(2155898233/5000000000 : ℝ)|=(2155898233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3689272683/10000000000 : ℝ)|^8401 ≤ (5350157604583/20000000000000 : ℝ)^6353
        have hw : |(3689272683/10000000000 : ℝ)|=(3689272683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007272509/2000000000 : ℝ)|^8401 ≤ (40372832214121/100000000000000 : ℝ)^6353
        have hw : |(1007272509/2000000000 : ℝ)|=(1007272509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035847543/5000000000 : ℝ)*x 0 + (5024682523/10000000000 : ℝ)*x 1 + (2837580989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035847543/5000000000 : ℝ)^8401 ≤ (6235935111373/50000000000000 : ℝ)^6353 := by
    have hnat : (1035847543 : ℕ)^8401*50000000000000^6353 ≤ 6235935111373^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035847543 5000000000 6235935111373 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024682523/10000000000 : ℝ)^8401 ≤ (20124532507391/50000000000000 : ℝ)^6353 := by
    have hnat : (5024682523 : ℕ)^8401*50000000000000^6353 ≤ 20124532507391^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024682523 10000000000 20124532507391 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837580989/5000000000 : ℝ)^8401 ≤ (11819766184743/25000000000000 : ℝ)^6353 := by
    have hnat : (2837580989 : ℕ)^8401*25000000000000^6353 ≤ 11819766184743^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837580989 5000000000 11819766184743 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035847543/5000000000 : ℝ), (5024682523/10000000000 : ℝ), (2837580989/5000000000 : ℝ)] ![(6235935111373/50000000000000 : ℝ), (20124532507391/50000000000000 : ℝ), (11819766184743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035847543/5000000000 : ℝ)|^8401 ≤ (6235935111373/50000000000000 : ℝ)^6353
        have hw : |(-1035847543/5000000000 : ℝ)|=(1035847543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024682523/10000000000 : ℝ)|^8401 ≤ (20124532507391/50000000000000 : ℝ)^6353
        have hw : |(5024682523/10000000000 : ℝ)|=(5024682523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2837580989/5000000000 : ℝ)|^8401 ≤ (11819766184743/25000000000000 : ℝ)^6353
        have hw : |(2837580989/5000000000 : ℝ)|=(2837580989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243576613/10000000000 : ℝ)*x 0 + (-442785919/2500000000 : ℝ)*x 1 + (5675159179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243576613/10000000000 : ℝ)^8401 ≤ (42583828682449/100000000000000 : ℝ)^6353 := by
    have hnat : (5243576613 : ℕ)^8401*100000000000000^6353 ≤ 42583828682449^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243576613 10000000000 42583828682449 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442785919/2500000000 : ℝ)^8401 ≤ (1013713740949/10000000000000 : ℝ)^6353 := by
    have hnat : (442785919 : ℕ)^8401*10000000000000^6353 ≤ 1013713740949^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442785919 2500000000 1013713740949 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675159179/10000000000 : ℝ)^8401 ≤ (9455806780771/20000000000000 : ℝ)^6353 := by
    have hnat : (5675159179 : ℕ)^8401*20000000000000^6353 ≤ 9455806780771^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675159179 10000000000 9455806780771 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243576613/10000000000 : ℝ), (-442785919/2500000000 : ℝ), (5675159179/10000000000 : ℝ)] ![(42583828682449/100000000000000 : ℝ), (1013713740949/10000000000000 : ℝ), (9455806780771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243576613/10000000000 : ℝ)|^8401 ≤ (42583828682449/100000000000000 : ℝ)^6353
        have hw : |(5243576613/10000000000 : ℝ)|=(5243576613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442785919/2500000000 : ℝ)|^8401 ≤ (1013713740949/10000000000000 : ℝ)^6353
        have hw : |(-442785919/2500000000 : ℝ)|=(442785919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675159179/10000000000 : ℝ)|^8401 ≤ (9455806780771/20000000000000 : ℝ)^6353
        have hw : |(5675159179/10000000000 : ℝ)|=(5675159179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621788377/5000000000 : ℝ)*x 0 + (5675159637/10000000000 : ℝ)*x 1 + (-221392851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621788377/5000000000 : ℝ)^8401 ≤ (21291915098333/50000000000000 : ℝ)^6353 := by
    have hnat : (2621788377 : ℕ)^8401*50000000000000^6353 ≤ 21291915098333^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621788377 5000000000 21291915098333 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675159637/10000000000 : ℝ)^8401 ≤ (236395194747/500000000000 : ℝ)^6353 := by
    have hnat : (5675159637 : ℕ)^8401*500000000000^6353 ≤ 236395194747^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675159637 10000000000 236395194747 500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221392851/1250000000 : ℝ)^8401 ≤ (5068565419987/50000000000000 : ℝ)^6353 := by
    have hnat : (221392851 : ℕ)^8401*50000000000000^6353 ≤ 5068565419987^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221392851 1250000000 5068565419987 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621788377/5000000000 : ℝ), (5675159637/10000000000 : ℝ), (-221392851/1250000000 : ℝ)] ![(21291915098333/50000000000000 : ℝ), (236395194747/500000000000 : ℝ), (5068565419987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621788377/5000000000 : ℝ)|^8401 ≤ (21291915098333/50000000000000 : ℝ)^6353
        have hw : |(2621788377/5000000000 : ℝ)|=(2621788377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675159637/10000000000 : ℝ)|^8401 ≤ (236395194747/500000000000 : ℝ)^6353
        have hw : |(5675159637/10000000000 : ℝ)|=(5675159637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221392851/1250000000 : ℝ)|^8401 ≤ (5068565419987/50000000000000 : ℝ)^6353
        have hw : |(-221392851/1250000000 : ℝ)|=(221392851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s1_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1078310671/2500000000 : ℝ)*x 0 + (1003686017/2000000000 : ℝ)*x 1 + (926887751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078310671/2500000000 : ℝ)^8401 ≤ (32890962348597/100000000000000 : ℝ)^6353 := by
    have hnat : (1078310671 : ℕ)^8401*100000000000000^6353 ≤ 32890962348597^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078310671 2500000000 32890962348597 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003686017/2000000000 : ℝ)^8401 ≤ (40182849226457/100000000000000 : ℝ)^6353 := by
    have hnat : (1003686017 : ℕ)^8401*100000000000000^6353 ≤ 40182849226457^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003686017 2000000000 40182849226457 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926887751/2500000000 : ℝ)^8401 ≤ (13463094204557/50000000000000 : ℝ)^6353 := by
    have hnat : (926887751 : ℕ)^8401*50000000000000^6353 ≤ 13463094204557^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926887751 2500000000 13463094204557 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078310671/2500000000 : ℝ), (1003686017/2000000000 : ℝ), (926887751/2500000000 : ℝ)] ![(32890962348597/100000000000000 : ℝ), (40182849226457/100000000000000 : ℝ), (13463094204557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078310671/2500000000 : ℝ)|^8401 ≤ (32890962348597/100000000000000 : ℝ)^6353
        have hw : |(1078310671/2500000000 : ℝ)|=(1078310671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003686017/2000000000 : ℝ)|^8401 ≤ (40182849226457/100000000000000 : ℝ)^6353
        have hw : |(1003686017/2000000000 : ℝ)|=(1003686017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926887751/2500000000 : ℝ)|^8401 ≤ (13463094204557/50000000000000 : ℝ)^6353
        have hw : |(926887751/2500000000 : ℝ)|=(926887751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6891/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4029/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6891/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6891/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6891/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6891/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6891/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6891/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (341/50000 : ℝ) ^ (525/128 : ℝ) ≤ (130356059609/100000000000000000000 : ℝ) := by
    have hpowers : (341/50000 : ℝ)^525 ≤ (130356059609/100000000000000000000 : ℝ)^128 := by
      have hnat : (341 : ℕ)^525*100000000000000000000^128 ≤ 130356059609^128*50000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        341 50000 130356059609 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (341/50000 : ℝ)) (X := (130356059609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (6891/25000 : ℝ) ^ (525/128 : ℝ) ≤ (506440843958564471/100000000000000000000 : ℝ) := by
    have hpowers : (6891/25000 : ℝ)^525 ≤ (506440843958564471/100000000000000000000 : ℝ)^128 := by
      have hnat : (6891 : ℕ)^525*100000000000000000000^128 ≤ 506440843958564471^128*25000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6891 25000 506440843958564471 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6891/25000 : ℝ)) (X := (506440843958564471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000130356059609/50000000000000000000 : ℝ) ≤ (1000000000635641/1000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50000000130356059609/50000000000000000000 : ℝ)^128 ≤ (1000000000635641/1000000000000000 : ℝ)^525 := by
      have hnat : (50000000130356059609 : ℕ)^128*1000000000000000^525 ≤ 1000000000635641^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000130356059609 50000000000000000000 1000000000635641 1000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000635641/1000000000000000 : ℝ)) (X := (50000000130356059609/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (1256330512178932801/1250000000000000000 : ℝ) ≤ (10012323939751057/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (1256330512178932801/1250000000000000000 : ℝ)^128 ≤ (10012323939751057/10000000000000000 : ℝ)^525 := by
      have hnat : (1256330512178932801 : ℕ)^128*10000000000000000^525 ≤ 10012323939751057^525*1250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1256330512178932801 1250000000000000000 10012323939751057 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012323939751057/10000000000000000 : ℝ)) (X := (1256330512178932801/1250000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50506440843958564471/50000000000000000000 : ℝ) ≤ (1253080984143213/1250000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50506440843958564471/50000000000000000000 : ℝ)^128 ≤ (1253080984143213/1250000000000000 : ℝ)^525 := by
      have hnat : (50506440843958564471 : ℕ)^128*1250000000000000^525 ≤ 1253080984143213^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50506440843958564471 50000000000000000000 1253080984143213 1250000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253080984143213/1250000000000000 : ℝ)) (X := (50506440843958564471/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(130356059609/100000000000000000000 : ℝ) ≤ ((33600398790715339389/33602500000000000000 : ℝ)+2*(12323933394647/2688200000000000 : ℝ)*(341/50000 : ℝ))^(525/128 : ℝ) := by
    rw [show (33600398790715339389/33602500000000000000 : ℝ)+2*(12323933394647/2688200000000000 : ℝ)*(341/50000 : ℝ)=(1000000000635641/1000000000000000 : ℝ) by norm_num, show 1+2*(130356059609/100000000000000000000 : ℝ)=(50000000130356059609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(506440843958564471/100000000000000000000 : ℝ)+(130356059609/100000000000000000000 : ℝ) ≤ ((33600398790715339389/33602500000000000000 : ℝ)+(12323933394647/2688200000000000 : ℝ)*((6891/25000 : ℝ)+(341/50000 : ℝ)))^(525/128 : ℝ) := by
    rw [show (33600398790715339389/33602500000000000000 : ℝ)+(12323933394647/2688200000000000 : ℝ)*((6891/25000 : ℝ)+(341/50000 : ℝ))=(10012323939751057/10000000000000000 : ℝ) by norm_num, show 1+(506440843958564471/100000000000000000000 : ℝ)+(130356059609/100000000000000000000 : ℝ)=(1256330512178932801/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(506440843958564471/100000000000000000000 : ℝ) ≤ ((33600398790715339389/33602500000000000000 : ℝ)+2*(12323933394647/2688200000000000 : ℝ)*(6891/25000 : ℝ))^(525/128 : ℝ) := by
    rw [show (33600398790715339389/33602500000000000000 : ℝ)+2*(12323933394647/2688200000000000 : ℝ)*(6891/25000 : ℝ)=(1253080984143213/1250000000000000 : ℝ) by norm_num, show 1+2*(506440843958564471/100000000000000000000 : ℝ)=(50506440843958564471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33600398790715339389/33602500000000000000 : ℝ)*(X 1 0+X 2 0)+(12323933394647/2688200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (341/50000 : ℝ)) (hi := (6891/25000 : ℝ)) (c := (33600398790715339389/33602500000000000000 : ℝ)) (alpha := (12323933394647/2688200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33600398790715339389/33602500000000000000 : ℝ)*(X 0 1+X 2 1)+(12323933394647/2688200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (341/50000 : ℝ)) (hi := (6891/25000 : ℝ)) (c := (33600398790715339389/33602500000000000000 : ℝ)) (alpha := (12323933394647/2688200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33600398790715339389/33602500000000000000 : ℝ)*(X 0 2+X 1 2)+(12323933394647/2688200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (341/50000 : ℝ)) (hi := (6891/25000 : ℝ)) (c := (33600398790715339389/33602500000000000000 : ℝ)) (alpha := (12323933394647/2688200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2070979287/10000000000 : ℝ)*X 0 0+(284211459/500000000 : ℝ)*X 0 1+(156743293/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415509367/10000000000 : ℝ)*X 1 0+(-2430517031/10000000000 : ℝ)*X 1 1+(5015785849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707754053/5000000000 : ℝ)*X 2 0+(2507893327/5000000000 : ℝ)*X 2 1+(-1215258823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155898233/5000000000 : ℝ)*X 0 0+(3689272683/10000000000 : ℝ)*X 0 1+(1007272509/2000000000 : ℝ)*X 0 2+(2155898233/5000000000 : ℝ)*X 1 0+(3689272683/10000000000 : ℝ)*X 1 1+(1007272509/2000000000 : ℝ)*X 1 2+(2155898233/5000000000 : ℝ)*X 2 0+(3689272683/10000000000 : ℝ)*X 2 1+(1007272509/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1035847543/5000000000 : ℝ)*X 0 0+(5024682523/10000000000 : ℝ)*X 0 1+(2837580989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243576613/10000000000 : ℝ)*X 1 0+(-442785919/2500000000 : ℝ)*X 1 1+(5675159179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621788377/5000000000 : ℝ)*X 2 0+(5675159637/10000000000 : ℝ)*X 2 1+(-221392851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078310671/2500000000 : ℝ)*X 0 0+(1003686017/2000000000 : ℝ)*X 0 1+(926887751/2500000000 : ℝ)*X 0 2+(1078310671/2500000000 : ℝ)*X 1 0+(1003686017/2000000000 : ℝ)*X 1 1+(926887751/2500000000 : ℝ)*X 1 2+(1078310671/2500000000 : ℝ)*X 2 0+(1003686017/2000000000 : ℝ)*X 2 1+(926887751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (982793797667413284947667633/210015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124172791/10000000000000 : ℝ)*(base19) + (463450067/50000000000000 : ℝ)*(base23) + (42638991/100000000000000 : ℝ)*(upper2) + (18120799/6250000000000 : ℝ)*(upper3) + (6121319/25000000000000 : ℝ)*(upper4) + (17487323033251/1562500000000 : ℝ)*(major0) + (17487323033251/1562500000000 : ℝ)*(major1) + (17487323033251/1562500000000 : ℝ)*(major2) + (1496021762593083/100000000000000 : ℝ)*(sp0) + (374006645788397/25000000000000 : ℝ)*(sp1) + (374006724495341/25000000000000 : ℝ)*(sp2) + (742344656667591/100000000000000 : ℝ)*(sp3) + (1212457683/20000000000000 : ℝ)*(sp4) + (37685757/800000000000 : ℝ)*(sp7) + (46396835461701/6250000000000 : ℝ)*(f.failure) + (748013912440749/50000000000000 : ℝ)*(f.sum) + (399312053760729/67205000000000000000000000000 : ℝ)*base65 + (1581309285955852319/210015625000000000000000000000000 : ℝ)*base68 + (416227425866946069/210015625000000000000000000000000 : ℝ)*base70 + (104155351556824597/105007812500000000000000000000000 : ℝ)*base72 + (19451465355523/33602500000000000000000000000 : ℝ)*base74 + (1772075098024664819/210015625000000000000000000000000 : ℝ)*base76 + (268521748029543347/105007812500000000000000000000000 : ℝ)*base78 + (1000805000456918347/105007812500000000000000000000000 : ℝ)*base80 + (229043007712249/67205000000000000000000000000 : ℝ)*base81 + (3796967/625000000000000000000 : ℝ)*base89 + (3796967/625000000000000000000 : ℝ)*base91 + (3796967/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2306704788684503464448068959/210015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120629823/100000000000000 : ℝ)*(base1) + (901831639/50000000000000 : ℝ)*(base19) + (188285873/10000000000000 : ℝ)*(base23) + (206737457/50000000000000 : ℝ)*(base32) + (137866803/100000000000000 : ℝ)*(upper5) + (143760827246541/12500000000000 : ℝ)*(major0) + (143760827246541/12500000000000 : ℝ)*(major1) + (143760827246541/12500000000000 : ℝ)*(major2) + (853227883/20000000000000 : ℝ)*(sp1) + (108414593/2000000000000 : ℝ)*(sp2) + (1537329251034619/100000000000000 : ℝ)*(sp4) + (1537323060602103/100000000000000 : ℝ)*(sp5) + (48041307088013/3125000000000 : ℝ)*(sp6) + (95355400664843/12500000000000 : ℝ)*(sp7) + (762843739423481/100000000000000 : ℝ)*(f.failure) + (384332282601199/25000000000000 : ℝ)*(f.sum) + (48568625772199/33602500000000000000000000000 : ℝ)*base65 + (1565979553271109699/420031250000000000000000000000000 : ℝ)*base67 + (760671118926703449/420031250000000000000000000000000 : ℝ)*base69 + (2559517539268515949/420031250000000000000000000000000 : ℝ)*base71 + (43541325536973/67205000000000000000000000000 : ℝ)*base73 + (1258502493395765949/420031250000000000000000000000000 : ℝ)*base75 + (2171862667646015949/420031250000000000000000000000000 : ℝ)*base77 + (748166799535015949/420031250000000000000000000000000 : ℝ)*base79 + (9166719870471/8400625000000000000000000000 : ℝ)*base81 + (7376227/10000000000000000000000 : ℝ)*base89 + (7376227/10000000000000000000000 : ℝ)*base91 + (7376227/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1208_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6891/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4029/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1208_s2_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120742383/10000000000 : ℝ)*x 0 + (1374675549/2500000000 : ℝ)*x 1 + (1033921553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120742383/10000000000 : ℝ)^8401 ≤ (12863809090623/100000000000000 : ℝ)^6353 := by
    have hnat : (2120742383 : ℕ)^8401*100000000000000^6353 ≤ 12863809090623^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120742383 10000000000 12863809090623 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374675549/2500000000 : ℝ)^8401 ≤ (5668113941801/12500000000000 : ℝ)^6353 := by
    have hnat : (1374675549 : ℕ)^8401*12500000000000^6353 ≤ 5668113941801^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374675549 2500000000 5668113941801 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033921553/2000000000 : ℝ)^8401 ≤ (10447819839761/25000000000000 : ℝ)^6353 := by
    have hnat : (1033921553 : ℕ)^8401*25000000000000^6353 ≤ 10447819839761^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033921553 2000000000 10447819839761 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120742383/10000000000 : ℝ), (1374675549/2500000000 : ℝ), (1033921553/2000000000 : ℝ)] ![(12863809090623/100000000000000 : ℝ), (5668113941801/12500000000000 : ℝ), (10447819839761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120742383/10000000000 : ℝ)|^8401 ≤ (12863809090623/100000000000000 : ℝ)^6353
        have hw : |(-2120742383/10000000000 : ℝ)|=(2120742383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374675549/2500000000 : ℝ)|^8401 ≤ (5668113941801/12500000000000 : ℝ)^6353
        have hw : |(1374675549/2500000000 : ℝ)|=(1374675549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033921553/2000000000 : ℝ)|^8401 ≤ (10447819839761/25000000000000 : ℝ)^6353
        have hw : |(1033921553/2000000000 : ℝ)|=(1033921553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685540453/5000000000 : ℝ)*x 0 + (-1145706389/5000000000 : ℝ)*x 1 + (413569/800000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685540453/5000000000 : ℝ)^8401 ≤ (21979225906909/50000000000000 : ℝ)^6353 := by
    have hnat : (2685540453 : ℕ)^8401*50000000000000^6353 ≤ 21979225906909^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685540453 5000000000 21979225906909 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145706389/5000000000 : ℝ)^8401 ≤ (570008727953/4000000000000 : ℝ)^6353 := by
    have hnat : (1145706389 : ℕ)^8401*4000000000000^6353 ≤ 570008727953^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145706389 5000000000 570008727953 4000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413569/800000 : ℝ)^8401 ≤ (41791329976493/100000000000000 : ℝ)^6353 := by
    have hnat : (413569 : ℕ)^8401*100000000000000^6353 ≤ 41791329976493^6353*800000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413569 800000 41791329976493 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685540453/5000000000 : ℝ), (-1145706389/5000000000 : ℝ), (413569/800000 : ℝ)] ![(21979225906909/50000000000000 : ℝ), (570008727953/4000000000000 : ℝ), (41791329976493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685540453/5000000000 : ℝ)|^8401 ≤ (21979225906909/50000000000000 : ℝ)^6353
        have hw : |(2685540453/5000000000 : ℝ)|=(2685540453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1145706389/5000000000 : ℝ)|^8401 ≤ (570008727953/4000000000000 : ℝ)^6353
        have hw : |(-1145706389/5000000000 : ℝ)|=(1145706389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413569/800000 : ℝ)|^8401 ≤ (41791329976493/100000000000000 : ℝ)^6353
        have hw : |(413569/800000 : ℝ)|=(413569/800000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371083061/10000000000 : ℝ)*x 0 + (5169609519/10000000000 : ℝ)*x 1 + (-286426727/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371083061/10000000000 : ℝ)^8401 ≤ (10989618784147/25000000000000 : ℝ)^6353 := by
    have hnat : (5371083061 : ℕ)^8401*25000000000000^6353 ≤ 10989618784147^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371083061 10000000000 10989618784147 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169609519/10000000000 : ℝ)^8401 ≤ (41791298109413/100000000000000 : ℝ)^6353 := by
    have hnat : (5169609519 : ℕ)^8401*100000000000000^6353 ≤ 41791298109413^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169609519 10000000000 41791298109413 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286426727/1250000000 : ℝ)^8401 ≤ (7125113367543/50000000000000 : ℝ)^6353 := by
    have hnat : (286426727 : ℕ)^8401*50000000000000^6353 ≤ 7125113367543^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286426727 1250000000 7125113367543 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371083061/10000000000 : ℝ), (5169609519/10000000000 : ℝ), (-286426727/1250000000 : ℝ)] ![(10989618784147/25000000000000 : ℝ), (41791298109413/100000000000000 : ℝ), (7125113367543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371083061/10000000000 : ℝ)|^8401 ≤ (10989618784147/25000000000000 : ℝ)^6353
        have hw : |(5371083061/10000000000 : ℝ)|=(5371083061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169609519/10000000000 : ℝ)|^8401 ≤ (41791298109413/100000000000000 : ℝ)^6353
        have hw : |(5169609519/10000000000 : ℝ)|=(5169609519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-286426727/1250000000 : ℝ)|^8401 ≤ (7125113367543/50000000000000 : ℝ)^6353
        have hw : |(-286426727/1250000000 : ℝ)|=(286426727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869218819/2000000000 : ℝ)*x 0 + (4026838231/10000000000 : ℝ)*x 1 + (938009269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869218819/2000000000 : ℝ)^8401 ≤ (16611317919297/50000000000000 : ℝ)^6353 := by
    have hnat : (869218819 : ℕ)^8401*50000000000000^6353 ≤ 16611317919297^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869218819 2000000000 16611317919297 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026838231/10000000000 : ℝ)^8401 ≤ (15017150182963/50000000000000 : ℝ)^6353 := by
    have hnat : (4026838231 : ℕ)^8401*50000000000000^6353 ≤ 15017150182963^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026838231 10000000000 15017150182963 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938009269/2000000000 : ℝ)^8401 ≤ (7348612757289/20000000000000 : ℝ)^6353 := by
    have hnat : (938009269 : ℕ)^8401*20000000000000^6353 ≤ 7348612757289^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938009269 2000000000 7348612757289 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869218819/2000000000 : ℝ), (4026838231/10000000000 : ℝ), (938009269/2000000000 : ℝ)] ![(16611317919297/50000000000000 : ℝ), (15017150182963/50000000000000 : ℝ), (7348612757289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869218819/2000000000 : ℝ)|^8401 ≤ (16611317919297/50000000000000 : ℝ)^6353
        have hw : |(869218819/2000000000 : ℝ)|=(869218819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026838231/10000000000 : ℝ)|^8401 ≤ (15017150182963/50000000000000 : ℝ)^6353
        have hw : |(4026838231/10000000000 : ℝ)|=(4026838231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(938009269/2000000000 : ℝ)|^8401 ≤ (7348612757289/20000000000000 : ℝ)^6353
        have hw : |(938009269/2000000000 : ℝ)|=(938009269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120826927/10000000000 : ℝ)*x 0 + (5171775911/10000000000 : ℝ)*x 1 + (5496514289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120826927/10000000000 : ℝ)^8401 ≤ (2572897446131/20000000000000 : ℝ)^6353 := by
    have hnat : (2120826927 : ℕ)^8401*20000000000000^6353 ≤ 2572897446131^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120826927 10000000000 2572897446131 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171775911/10000000000 : ℝ)^8401 ≤ (20907229269877/50000000000000 : ℝ)^6353 := by
    have hnat : (5171775911 : ℕ)^8401*50000000000000^6353 ≤ 20907229269877^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171775911 10000000000 20907229269877 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496514289/10000000000 : ℝ)^8401 ≤ (11330263555877/25000000000000 : ℝ)^6353 := by
    have hnat : (5496514289 : ℕ)^8401*25000000000000^6353 ≤ 11330263555877^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496514289 10000000000 11330263555877 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120826927/10000000000 : ℝ), (5171775911/10000000000 : ℝ), (5496514289/10000000000 : ℝ)] ![(2572897446131/20000000000000 : ℝ), (20907229269877/50000000000000 : ℝ), (11330263555877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120826927/10000000000 : ℝ)|^8401 ≤ (2572897446131/20000000000000 : ℝ)^6353
        have hw : |(-2120826927/10000000000 : ℝ)|=(2120826927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171775911/10000000000 : ℝ)|^8401 ≤ (20907229269877/50000000000000 : ℝ)^6353
        have hw : |(5171775911/10000000000 : ℝ)|=(5171775911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496514289/10000000000 : ℝ)|^8401 ≤ (11330263555877/25000000000000 : ℝ)^6353
        have hw : |(5496514289/10000000000 : ℝ)|=(5496514289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287221199/10000000000 : ℝ)*x 0 + (-491127323/2500000000 : ℝ)*x 1 + (1099302863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287221199/10000000000 : ℝ)^8401 ≤ (21526580665121/50000000000000 : ℝ)^6353 := by
    have hnat : (5287221199 : ℕ)^8401*50000000000000^6353 ≤ 21526580665121^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287221199 10000000000 21526580665121 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491127323/2500000000 : ℝ)^8401 ≤ (11625784147241/100000000000000 : ℝ)^6353 := by
    have hnat : (491127323 : ℕ)^8401*100000000000000^6353 ≤ 11625784147241^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491127323 2500000000 11625784147241 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099302863/2000000000 : ℝ)^8401 ≤ (22660527253499/50000000000000 : ℝ)^6353 := by
    have hnat : (1099302863 : ℕ)^8401*50000000000000^6353 ≤ 22660527253499^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099302863 2000000000 22660527253499 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287221199/10000000000 : ℝ), (-491127323/2500000000 : ℝ), (1099302863/2000000000 : ℝ)] ![(21526580665121/50000000000000 : ℝ), (11625784147241/100000000000000 : ℝ), (22660527253499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287221199/10000000000 : ℝ)|^8401 ≤ (21526580665121/50000000000000 : ℝ)^6353
        have hw : |(5287221199/10000000000 : ℝ)|=(5287221199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491127323/2500000000 : ℝ)|^8401 ≤ (11625784147241/100000000000000 : ℝ)^6353
        have hw : |(-491127323/2500000000 : ℝ)|=(491127323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099302863/2000000000 : ℝ)|^8401 ≤ (22660527253499/50000000000000 : ℝ)^6353
        have hw : |(1099302863/2000000000 : ℝ)|=(1099302863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643610689/5000000000 : ℝ)*x 0 + (5496514343/10000000000 : ℝ)*x 1 + (-982254503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643610689/5000000000 : ℝ)^8401 ≤ (4305316325769/10000000000000 : ℝ)^6353 := by
    have hnat : (2643610689 : ℕ)^8401*10000000000000^6353 ≤ 4305316325769^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643610689 5000000000 4305316325769 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496514343/10000000000 : ℝ)^8401 ≤ (9064210962459/20000000000000 : ℝ)^6353 := by
    have hnat : (5496514343 : ℕ)^8401*20000000000000^6353 ≤ 9064210962459^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496514343 10000000000 9064210962459 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982254503/5000000000 : ℝ)^8401 ≤ (5812890954553/50000000000000 : ℝ)^6353 := by
    have hnat : (982254503 : ℕ)^8401*50000000000000^6353 ≤ 5812890954553^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982254503 5000000000 5812890954553 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643610689/5000000000 : ℝ), (5496514343/10000000000 : ℝ), (-982254503/5000000000 : ℝ)] ![(4305316325769/10000000000000 : ℝ), (9064210962459/20000000000000 : ℝ), (5812890954553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643610689/5000000000 : ℝ)|^8401 ≤ (4305316325769/10000000000000 : ℝ)^6353
        have hw : |(2643610689/5000000000 : ℝ)|=(2643610689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496514343/10000000000 : ℝ)|^8401 ≤ (9064210962459/20000000000000 : ℝ)^6353
        have hw : |(5496514343/10000000000 : ℝ)|=(5496514343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982254503/5000000000 : ℝ)|^8401 ≤ (5812890954553/50000000000000 : ℝ)^6353
        have hw : |(-982254503/5000000000 : ℝ)|=(982254503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s2_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173133467/5000000000 : ℝ)*x 0 + (4685679641/10000000000 : ℝ)*x 1 + (4031246303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173133467/5000000000 : ℝ)^8401 ≤ (16612191497167/50000000000000 : ℝ)^6353 := by
    have hnat : (2173133467 : ℕ)^8401*50000000000000^6353 ≤ 16612191497167^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173133467 5000000000 16612191497167 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4685679641/10000000000 : ℝ)^8401 ≤ (36697832501857/100000000000000 : ℝ)^6353 := by
    have hnat : (4685679641 : ℕ)^8401*100000000000000^6353 ≤ 36697832501857^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4685679641 10000000000 36697832501857 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031246303/10000000000 : ℝ)^8401 ≤ (7519446123049/25000000000000 : ℝ)^6353 := by
    have hnat : (4031246303 : ℕ)^8401*25000000000000^6353 ≤ 7519446123049^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031246303 10000000000 7519446123049 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173133467/5000000000 : ℝ), (4685679641/10000000000 : ℝ), (4031246303/10000000000 : ℝ)] ![(16612191497167/50000000000000 : ℝ), (36697832501857/100000000000000 : ℝ), (7519446123049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173133467/5000000000 : ℝ)|^8401 ≤ (16612191497167/50000000000000 : ℝ)^6353
        have hw : |(2173133467/5000000000 : ℝ)|=(2173133467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4685679641/10000000000 : ℝ)|^8401 ≤ (36697832501857/100000000000000 : ℝ)^6353
        have hw : |(4685679641/10000000000 : ℝ)|=(4685679641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031246303/10000000000 : ℝ)|^8401 ≤ (7519446123049/25000000000000 : ℝ)^6353
        have hw : |(4031246303/10000000000 : ℝ)|=(4031246303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4029/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8157/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4029/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4029/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4029/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4029/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4029/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4029/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6011/100000 : ℝ) ^ (525/128 : ℝ) ≤ (98123648695989/10000000000000000000 : ℝ) := by
    have hpowers : (6011/100000 : ℝ)^525 ≤ (98123648695989/10000000000000000000 : ℝ)^128 := by
      have hnat : (6011 : ℕ)^525*10000000000000000000^128 ≤ 98123648695989^128*100000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6011 100000 98123648695989 10000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6011/100000 : ℝ)) (X := (98123648695989/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (4029/20000 : ℝ) ^ (525/128 : ℝ) ≤ (139958273166945807/100000000000000000000 : ℝ) := by
    have hpowers : (4029/20000 : ℝ)^525 ≤ (139958273166945807/100000000000000000000 : ℝ)^128 := by
      have hnat : (4029 : ℕ)^525*100000000000000000000^128 ≤ 139958273166945807^128*20000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4029 20000 139958273166945807 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4029/20000 : ℝ)) (X := (139958273166945807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000098123648695989/5000000000000000000 : ℝ) ≤ (2000009569321021/2000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (5000098123648695989/5000000000000000000 : ℝ)^128 ≤ (2000009569321021/2000000000000000 : ℝ)^525 := by
      have hnat : (5000098123648695989 : ℕ)^128*2000000000000000^525 ≤ 2000009569321021^525*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000098123648695989 5000000000000000000 2000009569321021 2000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009569321021/2000000000000000 : ℝ)) (X := (5000098123648695989/5000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100140939509653905697/100000000000000000000 : ℝ) ≤ (10003434409860333/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (100140939509653905697/100000000000000000000 : ℝ)^128 ≤ (10003434409860333/10000000000000000 : ℝ)^525 := by
      have hnat : (100140939509653905697 : ℕ)^128*10000000000000000^525 ≤ 10003434409860333^525*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100140939509653905697 100000000000000000000 10003434409860333 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003434409860333/10000000000000000 : ℝ)) (X := (100140939509653905697/100000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50139958273166945807/50000000000000000000 : ℝ) ≤ (10006820973115561/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50139958273166945807/50000000000000000000 : ℝ)^128 ≤ (10006820973115561/10000000000000000 : ℝ)^525 := by
      have hnat : (50139958273166945807 : ℕ)^128*10000000000000000^525 ≤ 10006820973115561^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50139958273166945807 50000000000000000000 10006820973115561 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006820973115561/10000000000000000 : ℝ)) (X := (50139958273166945807/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(98123648695989/10000000000000000000 : ℝ) ≤ ((70649981500231101527/70670000000000000000 : ℝ)+2*(846640813807/353350000000000 : ℝ)*(6011/100000 : ℝ))^(525/128 : ℝ) := by
    rw [show (70649981500231101527/70670000000000000000 : ℝ)+2*(846640813807/353350000000000 : ℝ)*(6011/100000 : ℝ)=(2000009569321021/2000000000000000 : ℝ) by norm_num, show 1+2*(98123648695989/10000000000000000000 : ℝ)=(5000098123648695989/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(139958273166945807/100000000000000000000 : ℝ)+(98123648695989/10000000000000000000 : ℝ) ≤ ((70649981500231101527/70670000000000000000 : ℝ)+(846640813807/353350000000000 : ℝ)*((4029/20000 : ℝ)+(6011/100000 : ℝ)))^(525/128 : ℝ) := by
    rw [show (70649981500231101527/70670000000000000000 : ℝ)+(846640813807/353350000000000 : ℝ)*((4029/20000 : ℝ)+(6011/100000 : ℝ))=(10003434409860333/10000000000000000 : ℝ) by norm_num, show 1+(139958273166945807/100000000000000000000 : ℝ)+(98123648695989/10000000000000000000 : ℝ)=(100140939509653905697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(139958273166945807/100000000000000000000 : ℝ) ≤ ((70649981500231101527/70670000000000000000 : ℝ)+2*(846640813807/353350000000000 : ℝ)*(4029/20000 : ℝ))^(525/128 : ℝ) := by
    rw [show (70649981500231101527/70670000000000000000 : ℝ)+2*(846640813807/353350000000000 : ℝ)*(4029/20000 : ℝ)=(10006820973115561/10000000000000000 : ℝ) by norm_num, show 1+2*(139958273166945807/100000000000000000000 : ℝ)=(50139958273166945807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70649981500231101527/70670000000000000000 : ℝ)*(X 1 0+X 2 0)+(846640813807/353350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (6011/100000 : ℝ)) (hi := (4029/20000 : ℝ)) (c := (70649981500231101527/70670000000000000000 : ℝ)) (alpha := (846640813807/353350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70649981500231101527/70670000000000000000 : ℝ)*(X 0 1+X 2 1)+(846640813807/353350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (6011/100000 : ℝ)) (hi := (4029/20000 : ℝ)) (c := (70649981500231101527/70670000000000000000 : ℝ)) (alpha := (846640813807/353350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70649981500231101527/70670000000000000000 : ℝ)*(X 0 2+X 1 2)+(846640813807/353350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (6011/100000 : ℝ)) (hi := (4029/20000 : ℝ)) (c := (70649981500231101527/70670000000000000000 : ℝ)) (alpha := (846640813807/353350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2120742383/10000000000 : ℝ)*X 0 0+(1374675549/2500000000 : ℝ)*X 0 1+(1033921553/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685540453/5000000000 : ℝ)*X 1 0+(-1145706389/5000000000 : ℝ)*X 1 1+(413569/800000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371083061/10000000000 : ℝ)*X 2 0+(5169609519/10000000000 : ℝ)*X 2 1+(-286426727/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869218819/2000000000 : ℝ)*X 0 0+(4026838231/10000000000 : ℝ)*X 0 1+(938009269/2000000000 : ℝ)*X 0 2+(869218819/2000000000 : ℝ)*X 1 0+(4026838231/10000000000 : ℝ)*X 1 1+(938009269/2000000000 : ℝ)*X 1 2+(869218819/2000000000 : ℝ)*X 2 0+(4026838231/10000000000 : ℝ)*X 2 1+(938009269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120826927/10000000000 : ℝ)*X 0 0+(5171775911/10000000000 : ℝ)*X 0 1+(5496514289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287221199/10000000000 : ℝ)*X 1 0+(-491127323/2500000000 : ℝ)*X 1 1+(1099302863/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643610689/5000000000 : ℝ)*X 2 0+(5496514343/10000000000 : ℝ)*X 2 1+(-982254503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173133467/5000000000 : ℝ)*X 0 0+(4685679641/10000000000 : ℝ)*X 0 1+(4031246303/10000000000 : ℝ)*X 0 2+(2173133467/5000000000 : ℝ)*X 1 0+(4685679641/10000000000 : ℝ)*X 1 1+(4031246303/10000000000 : ℝ)*X 1 2+(2173133467/5000000000 : ℝ)*X 2 0+(4685679641/10000000000 : ℝ)*X 2 1+(4031246303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7024661675298667810030409067/883375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (430117583/25000000000000 : ℝ)*(base19) + (1236597329/50000000000000 : ℝ)*(base23) + (33222487/50000000000000 : ℝ)*(upper2) + (794839319/100000000000000 : ℝ)*(upper3) + (158499167/50000000000000 : ℝ)*(upper4) + (1136650660307993/50000000000000 : ℝ)*(major0) + (1136650660307993/50000000000000 : ℝ)*(major1) + (1136650660307993/50000000000000 : ℝ)*(major2) + (3038693713457111/100000000000000 : ℝ)*(sp0) + (151936855733647/5000000000000 : ℝ)*(sp1) + (759684090487153/25000000000000 : ℝ)*(sp2) + (1507837847993707/100000000000000 : ℝ)*(sp3) + (564021077/1250000000000 : ℝ)*(sp4) + (5138605183/20000000000000 : ℝ)*(sp7) + (753931770509811/50000000000000 : ℝ)*(f.failure) + (3038738835143271/100000000000000 : ℝ)*(f.sum) + (66465562414083/17667500000000000000000000000 : ℝ)*base66 + (16087634341684805311/3533500000000000000000000000000000 : ℝ)*base67 + (23610865844290305311/3533500000000000000000000000000000 : ℝ)*base69 + (6821184182059694689/3533500000000000000000000000000000 : ℝ)*base72 + (39634238052721/8833750000000000000000000000 : ℝ)*base73 + (3108994101482805311/3533500000000000000000000000000000 : ℝ)*base75 + (12977801843258305311/3533500000000000000000000000000000 : ℝ)*base77 + (26736083540932805311/3533500000000000000000000000000000 : ℝ)*base79 + (21813134546281/8833750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (40049663/5000000000000000000000 : ℝ)*base90 + (40049663/5000000000000000000000 : ℝ)*base92 + (40049663/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122905985623244799655665783/27605468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (38208841/3125000000000 : ℝ)*(base19) + (1475602169/100000000000000 : ℝ)*(base23) + (304941/800000000000 : ℝ)*(upper2) + (84970361/50000000000000 : ℝ)*(upper3) + (45512511/50000000000000 : ℝ)*(upper5) + (71991268528749/3125000000000 : ℝ)*(major0) + (71991268528749/3125000000000 : ℝ)*(major1) + (71991268528749/3125000000000 : ℝ)*(major2) + (5945198231/50000000000000 : ℝ)*(sp1) + (4179431157/25000000000000 : ℝ)*(sp2) + (307940062358201/10000000000000 : ℝ)*(sp4) + (615877502100527/20000000000000 : ℝ)*(sp5) + (3079382430255213/100000000000000 : ℝ)*(sp6) + (1528040413850143/100000000000000 : ℝ)*(sp7) + (1528040413850143/100000000000000 : ℝ)*(f.failure) + (307940062358201/10000000000000 : ℝ)*(f.sum) + (4986472750367/8833750000000000000000000000 : ℝ)*base66 + (3163880614567569027/220843750000000000000000000000000 : ℝ)*base68 + (1656536431938881527/220843750000000000000000000000000 : ℝ)*base70 + (1747849421618881527/220843750000000000000000000000000 : ℝ)*base72 + (117752270488993/35335000000000000000000000000 : ℝ)*base74 + (1149778234190287777/220843750000000000000000000000000 : ℝ)*base76 + (2928779547846850277/220843750000000000000000000000000 : ℝ)*base78 + (3270679079880912777/220843750000000000000000000000000 : ℝ)*base80 + (74968360219347/35335000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (37068581/10000000000000000000000 : ℝ)*base89 + (37068581/10000000000000000000000 : ℝ)*base91 + (37068581/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1208_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4029/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1208_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1208_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1208_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1208_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1208_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

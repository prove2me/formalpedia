-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1518_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:33.06195+00:00
-- url     : https://prove2.me/submissions/53b949a2-a380-40f6-beb1-f77696effc0f

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
theorem support_rectangle_w1518_s0_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1679488953/10000000000 : ℝ)*x 0 + (5908223717/10000000000 : ℝ)*x 1 + (971575039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1679488953/10000000000 : ℝ)^4533 ≤ (9978552545961/100000000000000 : ℝ)^3509 := by
    have hnat : (1679488953 : ℕ)^4533*100000000000000^3509 ≤ 9978552545961^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679488953 10000000000 9978552545961 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5908223717/10000000000 : ℝ)^4533 ≤ (25335720658263/50000000000000 : ℝ)^3509 := by
    have hnat : (5908223717 : ℕ)^4533*50000000000000^3509 ≤ 25335720658263^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5908223717 10000000000 25335720658263 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971575039/2000000000 : ℝ)^4533 ≤ (787000122517/2000000000000 : ℝ)^3509 := by
    have hnat : (971575039 : ℕ)^4533*2000000000000^3509 ≤ 787000122517^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971575039 2000000000 787000122517 2000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1679488953/10000000000 : ℝ), (5908223717/10000000000 : ℝ), (971575039/2000000000 : ℝ)] ![(9978552545961/100000000000000 : ℝ), (25335720658263/50000000000000 : ℝ), (787000122517/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1679488953/10000000000 : ℝ)|^4533 ≤ (9978552545961/100000000000000 : ℝ)^3509
        have hw : |(-1679488953/10000000000 : ℝ)|=(1679488953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5908223717/10000000000 : ℝ)|^4533 ≤ (25335720658263/50000000000000 : ℝ)^3509
        have hw : |(5908223717/10000000000 : ℝ)|=(5908223717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(971575039/2000000000 : ℝ)|^4533 ≤ (787000122517/2000000000000 : ℝ)^3509
        have hw : |(971575039/2000000000 : ℝ)|=(971575039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2738337809/5000000000 : ℝ)*x 0 + (-141735991/625000000 : ℝ)*x 1 + (971575023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2738337809/5000000000 : ℝ)^4533 ≤ (45942093902321/100000000000000 : ℝ)^3509 := by
    have hnat : (2738337809 : ℕ)^4533*100000000000000^3509 ≤ 45942093902321^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738337809 5000000000 45942093902321 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141735991/625000000 : ℝ)^4533 ≤ (3676975196271/25000000000000 : ℝ)^3509 := by
    have hnat : (141735991 : ℕ)^4533*25000000000000^3509 ≤ 3676975196271^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141735991 625000000 3676975196271 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971575023/2000000000 : ℝ)^4533 ≤ (9837501322181/25000000000000 : ℝ)^3509 := by
    have hnat : (971575023 : ℕ)^4533*25000000000000^3509 ≤ 9837501322181^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971575023 2000000000 9837501322181 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2738337809/5000000000 : ℝ), (-141735991/625000000 : ℝ), (971575023/2000000000 : ℝ)] ![(45942093902321/100000000000000 : ℝ), (3676975196271/25000000000000 : ℝ), (9837501322181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2738337809/5000000000 : ℝ)|^4533 ≤ (45942093902321/100000000000000 : ℝ)^3509
        have hw : |(2738337809/5000000000 : ℝ)|=(2738337809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141735991/625000000 : ℝ)|^4533 ≤ (3676975196271/25000000000000 : ℝ)^3509
        have hw : |(-141735991/625000000 : ℝ)|=(141735991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(971575023/2000000000 : ℝ)|^4533 ≤ (9837501322181/25000000000000 : ℝ)^3509
        have hw : |(971575023/2000000000 : ℝ)|=(971575023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5476675701/10000000000 : ℝ)*x 0 + (2428937577/5000000000 : ℝ)*x 1 + (-22677757/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5476675701/10000000000 : ℝ)^4533 ≤ (9188418960353/20000000000000 : ℝ)^3509 := by
    have hnat : (5476675701 : ℕ)^4533*20000000000000^3509 ≤ 9188418960353^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476675701 10000000000 9188418960353 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2428937577/5000000000 : ℝ)^4533 ≤ (39350005696823/100000000000000 : ℝ)^3509 := by
    have hnat : (2428937577 : ℕ)^4533*100000000000000^3509 ≤ 39350005696823^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428937577 5000000000 39350005696823 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22677757/100000000 : ℝ)^4533 ≤ (7353949739039/50000000000000 : ℝ)^3509 := by
    have hnat : (22677757 : ℕ)^4533*50000000000000^3509 ≤ 7353949739039^3509*100000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22677757 100000000 7353949739039 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5476675701/10000000000 : ℝ), (2428937577/5000000000 : ℝ), (-22677757/100000000 : ℝ)] ![(9188418960353/20000000000000 : ℝ), (39350005696823/100000000000000 : ℝ), (7353949739039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5476675701/10000000000 : ℝ)|^4533 ≤ (9188418960353/20000000000000 : ℝ)^3509
        have hw : |(5476675701/10000000000 : ℝ)|=(5476675701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2428937577/5000000000 : ℝ)|^4533 ≤ (39350005696823/100000000000000 : ℝ)^3509
        have hw : |(2428937577/5000000000 : ℝ)|=(2428937577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22677757/100000000 : ℝ)|^4533 ≤ (7353949739039/50000000000000 : ℝ)^3509
        have hw : |(-22677757/100000000 : ℝ)|=(22677757/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64742653/156250000 : ℝ)*x 0 + (3091334131/10000000000 : ℝ)*x 1 + (5483162517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64742653/156250000 : ℝ)^4533 ≤ (32041373196297/100000000000000 : ℝ)^3509 := by
    have hnat : (64742653 : ℕ)^4533*100000000000000^3509 ≤ 32041373196297^3509*156250000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64742653 156250000 32041373196297 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091334131/10000000000 : ℝ)^4533 ≤ (5486556077063/25000000000000 : ℝ)^3509 := by
    have hnat : (3091334131 : ℕ)^4533*25000000000000^3509 ≤ 5486556077063^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091334131 10000000000 5486556077063 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483162517/10000000000 : ℝ)^4533 ≤ (184049609901/400000000000 : ℝ)^3509 := by
    have hnat : (5483162517 : ℕ)^4533*400000000000^3509 ≤ 184049609901^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483162517 10000000000 184049609901 400000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64742653/156250000 : ℝ), (3091334131/10000000000 : ℝ), (5483162517/10000000000 : ℝ)] ![(32041373196297/100000000000000 : ℝ), (5486556077063/25000000000000 : ℝ), (184049609901/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64742653/156250000 : ℝ)|^4533 ≤ (32041373196297/100000000000000 : ℝ)^3509
        have hw : |(64742653/156250000 : ℝ)|=(64742653/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091334131/10000000000 : ℝ)|^4533 ≤ (5486556077063/25000000000000 : ℝ)^3509
        have hw : |(3091334131/10000000000 : ℝ)|=(3091334131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483162517/10000000000 : ℝ)|^4533 ≤ (184049609901/400000000000 : ℝ)^3509
        have hw : |(5483162517/10000000000 : ℝ)|=(5483162517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168295837/1000000000 : ℝ)*x 0 + (4884635939/10000000000 : ℝ)*x 1 + (2940252639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168295837/1000000000 : ℝ)^4533 ≤ (2501297306129/25000000000000 : ℝ)^3509 := by
    have hnat : (168295837 : ℕ)^4533*25000000000000^3509 ≤ 2501297306129^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168295837 1000000000 2501297306129 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4884635939/10000000000 : ℝ)^4533 ≤ (19815128659767/50000000000000 : ℝ)^3509 := by
    have hnat : (4884635939 : ℕ)^4533*50000000000000^3509 ≤ 19815128659767^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884635939 10000000000 19815128659767 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2940252639/5000000000 : ℝ)^4533 ≤ (12591138361787/25000000000000 : ℝ)^3509 := by
    have hnat : (2940252639 : ℕ)^4533*25000000000000^3509 ≤ 12591138361787^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2940252639 5000000000 12591138361787 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168295837/1000000000 : ℝ), (4884635939/10000000000 : ℝ), (2940252639/5000000000 : ℝ)] ![(2501297306129/25000000000000 : ℝ), (19815128659767/50000000000000 : ℝ), (12591138361787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168295837/1000000000 : ℝ)|^4533 ≤ (2501297306129/25000000000000 : ℝ)^3509
        have hw : |(-168295837/1000000000 : ℝ)|=(168295837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4884635939/10000000000 : ℝ)|^4533 ≤ (19815128659767/50000000000000 : ℝ)^3509
        have hw : |(4884635939/10000000000 : ℝ)|=(4884635939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2940252639/5000000000 : ℝ)|^4533 ≤ (12591138361787/25000000000000 : ℝ)^3509
        have hw : |(2940252639/5000000000 : ℝ)|=(2940252639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5189682359/10000000000 : ℝ)*x 0 + (-622572887/5000000000 : ℝ)*x 1 + (2940252661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189682359/10000000000 : ℝ)^4533 ≤ (42856121521179/100000000000000 : ℝ)^3509 := by
    have hnat : (5189682359 : ℕ)^4533*100000000000000^3509 ≤ 42856121521179^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189682359 10000000000 42856121521179 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622572887/5000000000 : ℝ)^4533 ≤ (67793245247/1000000000000 : ℝ)^3509 := by
    have hnat : (622572887 : ℕ)^4533*1000000000000^3509 ≤ 67793245247^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622572887 5000000000 67793245247 1000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2940252661/5000000000 : ℝ)^4533 ≤ (10072910786793/20000000000000 : ℝ)^3509 := by
    have hnat : (2940252661 : ℕ)^4533*20000000000000^3509 ≤ 10072910786793^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2940252661 5000000000 10072910786793 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189682359/10000000000 : ℝ), (-622572887/5000000000 : ℝ), (2940252661/5000000000 : ℝ)] ![(42856121521179/100000000000000 : ℝ), (67793245247/1000000000000 : ℝ), (10072910786793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189682359/10000000000 : ℝ)|^4533 ≤ (42856121521179/100000000000000 : ℝ)^3509
        have hw : |(5189682359/10000000000 : ℝ)|=(5189682359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-622572887/5000000000 : ℝ)|^4533 ≤ (67793245247/1000000000000 : ℝ)^3509
        have hw : |(-622572887/5000000000 : ℝ)|=(622572887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2940252661/5000000000 : ℝ)|^4533 ≤ (10072910786793/20000000000000 : ℝ)^3509
        have hw : |(2940252661/5000000000 : ℝ)|=(2940252661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64871029/125000000 : ℝ)*x 0 + (367531591/625000000 : ℝ)*x 1 + (-622572811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64871029/125000000 : ℝ)^4533 ≤ (8571224221027/20000000000000 : ℝ)^3509 := by
    have hnat : (64871029 : ℕ)^4533*20000000000000^3509 ≤ 8571224221027^3509*125000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64871029 125000000 8571224221027 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (367531591/625000000 : ℝ)^4533 ≤ (50364555416543/100000000000000 : ℝ)^3509 := by
    have hnat : (367531591 : ℕ)^4533*100000000000000^3509 ≤ 50364555416543^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367531591 625000000 50364555416543 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622572811/5000000000 : ℝ)^4533 ≤ (52963464497/781250000000 : ℝ)^3509 := by
    have hnat : (622572811 : ℕ)^4533*781250000000^3509 ≤ 52963464497^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622572811 5000000000 52963464497 781250000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64871029/125000000 : ℝ), (367531591/625000000 : ℝ), (-622572811/5000000000 : ℝ)] ![(8571224221027/20000000000000 : ℝ), (50364555416543/100000000000000 : ℝ), (52963464497/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64871029/125000000 : ℝ)|^4533 ≤ (8571224221027/20000000000000 : ℝ)^3509
        have hw : |(64871029/125000000 : ℝ)|=(64871029/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(367531591/625000000 : ℝ)|^4533 ≤ (50364555416543/100000000000000 : ℝ)^3509
        have hw : |(367531591/625000000 : ℝ)|=(367531591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-622572811/5000000000 : ℝ)|^4533 ≤ (52963464497/781250000000 : ℝ)^3509
        have hw : |(-622572811/5000000000 : ℝ)|=(622572811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s0_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4151430101/10000000000 : ℝ)*x 0 + (5422223521/10000000000 : ℝ)*x 1 + (197153377/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151430101/10000000000 : ℝ)^4533 ≤ (32120315143353/100000000000000 : ℝ)^3509 := by
    have hnat : (4151430101 : ℕ)^4533*100000000000000^3509 ≤ 32120315143353^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151430101 10000000000 32120315143353 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422223521/10000000000 : ℝ)^4533 ≤ (45352872190143/100000000000000 : ℝ)^3509 := by
    have hnat : (5422223521 : ℕ)^4533*100000000000000^3509 ≤ 45352872190143^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422223521 10000000000 45352872190143 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197153377/625000000 : ℝ)^4533 ≤ (5631703161759/25000000000000 : ℝ)^3509 := by
    have hnat : (197153377 : ℕ)^4533*25000000000000^3509 ≤ 5631703161759^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197153377 625000000 5631703161759 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151430101/10000000000 : ℝ), (5422223521/10000000000 : ℝ), (197153377/625000000 : ℝ)] ![(32120315143353/100000000000000 : ℝ), (45352872190143/100000000000000 : ℝ), (5631703161759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151430101/10000000000 : ℝ)|^4533 ≤ (32120315143353/100000000000000 : ℝ)^3509
        have hw : |(4151430101/10000000000 : ℝ)|=(4151430101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422223521/10000000000 : ℝ)|^4533 ≤ (45352872190143/100000000000000 : ℝ)^3509
        have hw : |(5422223521/10000000000 : ℝ)|=(5422223521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197153377/625000000 : ℝ)|^4533 ≤ (5631703161759/25000000000000 : ℝ)^3509
        have hw : |(197153377/625000000 : ℝ)|=(197153377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (363/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25407/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4531/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4531 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4531*1^1024 ≤ 0^1024*1^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4531/1024 : ℝ) ≤ (13876603245166051/800000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4531 ≤ (13876603245166051/800000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4531*800000000000000000^1024 ≤ 13876603245166051^1024*5^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 13876603245166051 800000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (13876603245166051/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4531 := by
      have hnat : (1 : ℕ)^1024*1^4531 ≤ 1^4531*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (813876603245166051/800000000000000000 : ℝ) ≤ (2509735172807359/2500000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (813876603245166051/800000000000000000 : ℝ)^1024 ≤ (2509735172807359/2500000000000000 : ℝ)^4531 := by
      have hnat : (813876603245166051 : ℕ)^1024*2500000000000000^4531 ≤ 2509735172807359^4531*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813876603245166051 800000000000000000 2509735172807359 2500000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509735172807359/2500000000000000 : ℝ)) (X := (813876603245166051/800000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (413876603245166051/400000000000000000 : ℝ) ≤ (1259735172807359/1250000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (413876603245166051/400000000000000000 : ℝ)^1024 ≤ (1259735172807359/1250000000000000 : ℝ)^4531 := by
      have hnat : (413876603245166051 : ℕ)^1024*1250000000000000^4531 ≤ 1259735172807359^4531*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413876603245166051 400000000000000000 1259735172807359 1250000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259735172807359/1250000000000000 : ℝ)) (X := (413876603245166051/400000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9735172807359/1000000000000000 : ℝ)*(0 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9735172807359/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13876603245166051/800000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9735172807359/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9735172807359/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509735172807359/2500000000000000 : ℝ) by norm_num, show 1+(13876603245166051/800000000000000000 : ℝ)+(0 : ℝ)=(813876603245166051/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13876603245166051/800000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9735172807359/1000000000000000 : ℝ)*(2/5 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9735172807359/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259735172807359/1250000000000000 : ℝ) by norm_num, show 1+2*(13876603245166051/800000000000000000 : ℝ)=(413876603245166051/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9735172807359/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9735172807359/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9735172807359/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9735172807359/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9735172807359/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9735172807359/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1679488953/10000000000 : ℝ)*X 0 0+(5908223717/10000000000 : ℝ)*X 0 1+(971575039/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2738337809/5000000000 : ℝ)*X 1 0+(-141735991/625000000 : ℝ)*X 1 1+(971575023/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5476675701/10000000000 : ℝ)*X 2 0+(2428937577/5000000000 : ℝ)*X 2 1+(-22677757/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((64742653/156250000 : ℝ)*X 0 0+(3091334131/10000000000 : ℝ)*X 0 1+(5483162517/10000000000 : ℝ)*X 0 2+(64742653/156250000 : ℝ)*X 1 0+(3091334131/10000000000 : ℝ)*X 1 1+(5483162517/10000000000 : ℝ)*X 1 2+(64742653/156250000 : ℝ)*X 2 0+(3091334131/10000000000 : ℝ)*X 2 1+(5483162517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-168295837/1000000000 : ℝ)*X 0 0+(4884635939/10000000000 : ℝ)*X 0 1+(2940252639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5189682359/10000000000 : ℝ)*X 1 0+(-622572887/5000000000 : ℝ)*X 1 1+(2940252661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((64871029/125000000 : ℝ)*X 2 0+(367531591/625000000 : ℝ)*X 2 1+(-622572811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4151430101/10000000000 : ℝ)*X 0 0+(5422223521/10000000000 : ℝ)*X 0 1+(197153377/625000000 : ℝ)*X 0 2+(4151430101/10000000000 : ℝ)*X 1 0+(5422223521/10000000000 : ℝ)*X 1 1+(197153377/625000000 : ℝ)*X 1 2+(4151430101/10000000000 : ℝ)*X 2 0+(5422223521/10000000000 : ℝ)*X 2 1+(197153377/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38017396672878330124257/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54928279/100000000000000 : ℝ)*(base1) + (70090791/4000000000000 : ℝ)*(base19) + (220837331/12500000000000 : ℝ)*(base23) + (202872231/100000000000000 : ℝ)*(upper3) + (125817051/50000000000000 : ℝ)*(upper5) + (137017316035553/20000000000000 : ℝ)*(major0) + (137017316035553/20000000000000 : ℝ)*(major1) + (137017316035553/20000000000000 : ℝ)*(major2) + (952070734336543/100000000000000 : ℝ)*(sp0) + (952075418896279/100000000000000 : ℝ)*(sp1) + (476037702233703/50000000000000 : ℝ)*(sp2) + (418092931420903/100000000000000 : ℝ)*(sp3) + (6491757789/100000000000000 : ℝ)*(sp4) + (1374695489/50000000000000 : ℝ)*(sp7) + (326637293547/78125000000 : ℝ)*(f.failure) + (476038585583027/50000000000000 : ℝ)*(f.sum) + (17866088584527/10000000000000000000000000000 : ℝ)*base65 + (66777203374527/20000000000000000000000000000 : ℝ)*base67 + (155621716554527/20000000000000000000000000000 : ℝ)*base69 + (77241336514527/20000000000000000000000000000 : ℝ)*base71 + (15596323964527/10000000000000000000000000000 : ℝ)*base73 + (39894999394527/20000000000000000000000000000 : ℝ)*base75 + (44911812834527/20000000000000000000000000000 : ℝ)*base77 + (83471976934527/20000000000000000000000000000 : ℝ)*base79 + (47751444564527/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10871/7812500000000000000 : ℝ)*base90 + (10871/7812500000000000000 : ℝ)*base92 + (10871/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (423454631484961659971199/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1890377867/100000000000000 : ℝ)*(base19) + (951182459/50000000000000 : ℝ)*(base23) + (17615789/25000000000000 : ℝ)*(base32) + (283825047/100000000000000 : ℝ)*(upper3) + (55501131/25000000000000 : ℝ)*(upper5) + (722554752964471/100000000000000 : ℝ)*(major0) + (722554752964471/100000000000000 : ℝ)*(major1) + (722554752964471/100000000000000 : ℝ)*(major2) + (4882834031/100000000000000 : ℝ)*(sp1) + (5236047989/100000000000000 : ℝ)*(sp2) + (1004147351368997/100000000000000 : ℝ)*(sp4) + (10041405781571/1000000000000 : ℝ)*(sp5) + (100414021295609/10000000000000 : ℝ)*(sp6) + (220480900896847/50000000000000 : ℝ)*(sp7) + (8819237445137/2000000000000 : ℝ)*(f.failure) + (1004147351368997/100000000000000 : ℝ)*(f.sum) + (87676244142089/50000000000000000000000000000 : ℝ)*base65 + (398586678642089/100000000000000000000000000000 : ℝ)*base67 + (292418616942089/100000000000000000000000000000 : ℝ)*base69 + (319618839142089/100000000000000000000000000000 : ℝ)*base71 + (44561372442089/50000000000000000000000000000 : ℝ)*base73 + (306387242957911/100000000000000000000000000000 : ℝ)*base76 + (427959936042089/100000000000000000000000000000 : ℝ)*base77 + (753425762342089/100000000000000000000000000000 : ℝ)*base79 + (94160792057911/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (678433/100000000000000000000 : ℝ)*base90 + (678433/100000000000000000000 : ℝ)*base92 + (678433/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1518_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25407/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1518_s1_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5723737/31250000 : ℝ)*x 0 + (173955033/312500000 : ℝ)*x 1 + (5101749571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5723737/31250000 : ℝ)^4533 ≤ (2790280375669/25000000000000 : ℝ)^3509 := by
    have hnat : (5723737 : ℕ)^4533*25000000000000^3509 ≤ 2790280375669^3509*31250000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5723737 31250000 2790280375669 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173955033/312500000 : ℝ)^4533 ≤ (46918476982733/100000000000000 : ℝ)^3509 := by
    have hnat : (173955033 : ℕ)^4533*100000000000000^3509 ≤ 46918476982733^3509*312500000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173955033 312500000 46918476982733 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5101749571/10000000000 : ℝ)^4533 ≤ (41920401503067/100000000000000 : ℝ)^3509 := by
    have hnat : (5101749571 : ℕ)^4533*100000000000000^3509 ≤ 41920401503067^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5101749571 10000000000 41920401503067 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5723737/31250000 : ℝ), (173955033/312500000 : ℝ), (5101749571/10000000000 : ℝ)] ![(2790280375669/25000000000000 : ℝ), (46918476982733/100000000000000 : ℝ), (41920401503067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5723737/31250000 : ℝ)|^4533 ≤ (2790280375669/25000000000000 : ℝ)^3509
        have hw : |(-5723737/31250000 : ℝ)|=(5723737/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173955033/312500000 : ℝ)|^4533 ≤ (46918476982733/100000000000000 : ℝ)^3509
        have hw : |(173955033/312500000 : ℝ)|=(173955033/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5101749571/10000000000 : ℝ)|^4533 ≤ (41920401503067/100000000000000 : ℝ)^3509
        have hw : |(5101749571/10000000000 : ℝ)|=(5101749571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385535353/10000000000 : ℝ)*x 0 + (-207616761/1000000000 : ℝ)*x 1 + (5101748943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385535353/10000000000 : ℝ)^4533 ≤ (22478422004161/50000000000000 : ℝ)^3509 := by
    have hnat : (5385535353 : ℕ)^4533*50000000000000^3509 ≤ 22478422004161^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385535353 10000000000 22478422004161 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207616761/1000000000 : ℝ)^4533 ≤ (13122761141847/100000000000000 : ℝ)^3509 := by
    have hnat : (207616761 : ℕ)^4533*100000000000000^3509 ≤ 13122761141847^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207616761 1000000000 13122761141847 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5101748943/10000000000 : ℝ)^4533 ≤ (20960197418511/50000000000000 : ℝ)^3509 := by
    have hnat : (5101748943 : ℕ)^4533*50000000000000^3509 ≤ 20960197418511^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5101748943 10000000000 20960197418511 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385535353/10000000000 : ℝ), (-207616761/1000000000 : ℝ), (5101748943/10000000000 : ℝ)] ![(22478422004161/50000000000000 : ℝ), (13122761141847/100000000000000 : ℝ), (20960197418511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385535353/10000000000 : ℝ)|^4533 ≤ (22478422004161/50000000000000 : ℝ)^3509
        have hw : |(5385535353/10000000000 : ℝ)|=(5385535353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207616761/1000000000 : ℝ)|^4533 ≤ (13122761141847/100000000000000 : ℝ)^3509
        have hw : |(-207616761/1000000000 : ℝ)|=(207616761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5101748943/10000000000 : ℝ)|^4533 ≤ (20960197418511/50000000000000 : ℝ)^3509
        have hw : |(5101748943/10000000000 : ℝ)|=(5101748943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385534857/10000000000 : ℝ)*x 0 + (5101749473/10000000000 : ℝ)*x 1 + (-259520947/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385534857/10000000000 : ℝ)^4533 ≤ (11239209664897/25000000000000 : ℝ)^3509 := by
    have hnat : (5385534857 : ℕ)^4533*25000000000000^3509 ≤ 11239209664897^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385534857 10000000000 11239209664897 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5101749473/10000000000 : ℝ)^4533 ≤ (5240050057853/12500000000000 : ℝ)^3509 := by
    have hnat : (5101749473 : ℕ)^4533*12500000000000^3509 ≤ 5240050057853^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5101749473 10000000000 5240050057853 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259520947/1250000000 : ℝ)^4533 ≤ (1640345108029/12500000000000 : ℝ)^3509 := by
    have hnat : (259520947 : ℕ)^4533*12500000000000^3509 ≤ 1640345108029^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259520947 1250000000 1640345108029 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385534857/10000000000 : ℝ), (5101749473/10000000000 : ℝ), (-259520947/1250000000 : ℝ)] ![(11239209664897/25000000000000 : ℝ), (5240050057853/12500000000000 : ℝ), (1640345108029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385534857/10000000000 : ℝ)|^4533 ≤ (11239209664897/25000000000000 : ℝ)^3509
        have hw : |(5385534857/10000000000 : ℝ)|=(5385534857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5101749473/10000000000 : ℝ)|^4533 ≤ (5240050057853/12500000000000 : ℝ)^3509
        have hw : |(5101749473/10000000000 : ℝ)|=(5101749473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259520947/1250000000 : ℝ)|^4533 ≤ (1640345108029/12500000000000 : ℝ)^3509
        have hw : |(-259520947/1250000000 : ℝ)|=(259520947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530927631/1250000000 : ℝ)*x 0 + (936474271/2500000000 : ℝ)*x 1 + (4804355123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530927631/1250000000 : ℝ)^4533 ≤ (1654148383791/5000000000000 : ℝ)^3509 := by
    have hnat : (530927631 : ℕ)^4533*5000000000000^3509 ≤ 1654148383791^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530927631 1250000000 1654148383791 5000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936474271/2500000000 : ℝ)^4533 ≤ (3515770193731/12500000000000 : ℝ)^3509 := by
    have hnat : (936474271 : ℕ)^4533*12500000000000^3509 ≤ 3515770193731^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936474271 2500000000 3515770193731 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4804355123/10000000000 : ℝ)^4533 ≤ (19395435378979/50000000000000 : ℝ)^3509 := by
    have hnat : (4804355123 : ℕ)^4533*50000000000000^3509 ≤ 19395435378979^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804355123 10000000000 19395435378979 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530927631/1250000000 : ℝ), (936474271/2500000000 : ℝ), (4804355123/10000000000 : ℝ)] ![(1654148383791/5000000000000 : ℝ), (3515770193731/12500000000000 : ℝ), (19395435378979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530927631/1250000000 : ℝ)|^4533 ≤ (1654148383791/5000000000000 : ℝ)^3509
        have hw : |(530927631/1250000000 : ℝ)|=(530927631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936474271/2500000000 : ℝ)|^4533 ≤ (3515770193731/12500000000000 : ℝ)^3509
        have hw : |(936474271/2500000000 : ℝ)|=(936474271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4804355123/10000000000 : ℝ)|^4533 ≤ (19395435378979/50000000000000 : ℝ)^3509
        have hw : |(4804355123/10000000000 : ℝ)|=(4804355123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-183188663/1000000000 : ℝ)*x 0 + (1276726031/2500000000 : ℝ)*x 1 + (5561324309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183188663/1000000000 : ℝ)^4533 ≤ (5581705315307/50000000000000 : ℝ)^3509 := by
    have hnat : (183188663 : ℕ)^4533*50000000000000^3509 ≤ 5581705315307^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183188663 1000000000 5581705315307 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276726031/2500000000 : ℝ)^4533 ≤ (5246890464651/12500000000000 : ℝ)^3509 := by
    have hnat : (1276726031 : ℕ)^4533*12500000000000^3509 ≤ 5246890464651^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276726031 2500000000 5246890464651 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5561324309/10000000000 : ℝ)^4533 ≤ (292884160273/625000000000 : ℝ)^3509 := by
    have hnat : (5561324309 : ℕ)^4533*625000000000^3509 ≤ 292884160273^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5561324309 10000000000 292884160273 625000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183188663/1000000000 : ℝ), (1276726031/2500000000 : ℝ), (5561324309/10000000000 : ℝ)] ![(5581705315307/50000000000000 : ℝ), (5246890464651/12500000000000 : ℝ), (292884160273/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183188663/1000000000 : ℝ)|^4533 ≤ (5581705315307/50000000000000 : ℝ)^3509
        have hw : |(-183188663/1000000000 : ℝ)|=(183188663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1276726031/2500000000 : ℝ)|^4533 ≤ (5246890464651/12500000000000 : ℝ)^3509
        have hw : |(1276726031/2500000000 : ℝ)|=(1276726031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5561324309/10000000000 : ℝ)|^4533 ≤ (292884160273/625000000000 : ℝ)^3509
        have hw : |(5561324309/10000000000 : ℝ)|=(5561324309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263018677/10000000000 : ℝ)*x 0 + (-1616592421/10000000000 : ℝ)*x 1 + (5561324437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263018677/10000000000 : ℝ)^4533 ≤ (43640065667007/100000000000000 : ℝ)^3509 := by
    have hnat : (5263018677 : ℕ)^4533*100000000000000^3509 ≤ 43640065667007^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263018677 10000000000 43640065667007 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1616592421/10000000000 : ℝ)^4533 ≤ (9498467280861/100000000000000 : ℝ)^3509 := by
    have hnat : (1616592421 : ℕ)^4533*100000000000000^3509 ≤ 9498467280861^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616592421 10000000000 9498467280861 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5561324437/10000000000 : ℝ)^4533 ≤ (46861467036997/100000000000000 : ℝ)^3509 := by
    have hnat : (5561324437 : ℕ)^4533*100000000000000^3509 ≤ 46861467036997^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5561324437 10000000000 46861467036997 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263018677/10000000000 : ℝ), (-1616592421/10000000000 : ℝ), (5561324437/10000000000 : ℝ)] ![(43640065667007/100000000000000 : ℝ), (9498467280861/100000000000000 : ℝ), (46861467036997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263018677/10000000000 : ℝ)|^4533 ≤ (43640065667007/100000000000000 : ℝ)^3509
        have hw : |(5263018677/10000000000 : ℝ)|=(5263018677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1616592421/10000000000 : ℝ)|^4533 ≤ (9498467280861/100000000000000 : ℝ)^3509
        have hw : |(-1616592421/10000000000 : ℝ)|=(1616592421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5561324437/10000000000 : ℝ)|^4533 ≤ (46861467036997/100000000000000 : ℝ)^3509
        have hw : |(5561324437/10000000000 : ℝ)|=(5561324437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657877303/1250000000 : ℝ)*x 0 + (1390331143/2500000000 : ℝ)*x 1 + (-202074073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657877303/1250000000 : ℝ)^4533 ≤ (43640062956981/100000000000000 : ℝ)^3509 := by
    have hnat : (657877303 : ℕ)^4533*100000000000000^3509 ≤ 43640062956981^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657877303 1250000000 43640062956981 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390331143/2500000000 : ℝ)^4533 ≤ (46861468506511/100000000000000 : ℝ)^3509 := by
    have hnat : (1390331143 : ℕ)^4533*100000000000000^3509 ≤ 46861468506511^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390331143 2500000000 46861468506511 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202074073/1250000000 : ℝ)^4533 ≤ (949846851807/10000000000000 : ℝ)^3509 := by
    have hnat : (202074073 : ℕ)^4533*10000000000000^3509 ≤ 949846851807^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202074073 1250000000 949846851807 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657877303/1250000000 : ℝ), (1390331143/2500000000 : ℝ), (-202074073/1250000000 : ℝ)] ![(43640062956981/100000000000000 : ℝ), (46861468506511/100000000000000 : ℝ), (949846851807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657877303/1250000000 : ℝ)|^4533 ≤ (43640062956981/100000000000000 : ℝ)^3509
        have hw : |(657877303/1250000000 : ℝ)|=(657877303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1390331143/2500000000 : ℝ)|^4533 ≤ (46861468506511/100000000000000 : ℝ)^3509
        have hw : |(1390331143/2500000000 : ℝ)|=(1390331143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202074073/1250000000 : ℝ)|^4533 ≤ (949846851807/10000000000000 : ℝ)^3509
        have hw : |(-202074073/1250000000 : ℝ)|=(202074073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s1_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124041909/5000000000 : ℝ)*x 0 + (4792617159/10000000000 : ℝ)*x 1 + (939455409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124041909/5000000000 : ℝ)^4533 ≤ (33089636576141/100000000000000 : ℝ)^3509 := by
    have hnat : (2124041909 : ℕ)^4533*100000000000000^3509 ≤ 33089636576141^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124041909 5000000000 33089636576141 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4792617159/10000000000 : ℝ)^4533 ≤ (3866848394843/10000000000000 : ℝ)^3509 := by
    have hnat : (4792617159 : ℕ)^4533*10000000000000^3509 ≤ 3866848394843^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792617159 10000000000 3866848394843 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939455409/2500000000 : ℝ)^4533 ≤ (14120939728957/50000000000000 : ℝ)^3509 := by
    have hnat : (939455409 : ℕ)^4533*50000000000000^3509 ≤ 14120939728957^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939455409 2500000000 14120939728957 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124041909/5000000000 : ℝ), (4792617159/10000000000 : ℝ), (939455409/2500000000 : ℝ)] ![(33089636576141/100000000000000 : ℝ), (3866848394843/10000000000000 : ℝ), (14120939728957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124041909/5000000000 : ℝ)|^4533 ≤ (33089636576141/100000000000000 : ℝ)^3509
        have hw : |(2124041909/5000000000 : ℝ)|=(2124041909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4792617159/10000000000 : ℝ)|^4533 ≤ (3866848394843/10000000000000 : ℝ)^3509
        have hw : |(4792617159/10000000000 : ℝ)|=(4792617159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(939455409/2500000000 : ℝ)|^4533 ≤ (14120939728957/50000000000000 : ℝ)^3509
        have hw : |(939455409/2500000000 : ℝ)|=(939455409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25407/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2109/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4567/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25407/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (363/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25407/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (363/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25407/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (363/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25407/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (363/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25407/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (363/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25407/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (363/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (363/12500 : ℝ) ^ (4531/1024 : ℝ) ≤ (197683406929/1250000000000000000 : ℝ) := by
    have hpowers : (363/12500 : ℝ)^4531 ≤ (197683406929/1250000000000000000 : ℝ)^1024 := by
      have hnat : (363 : ℕ)^4531*1250000000000000000^1024 ≤ 197683406929^1024*12500^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        363 12500 197683406929 1250000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (363/12500 : ℝ)) (X := (197683406929/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25407/100000 : ℝ) ^ (4531/1024 : ℝ) ≤ (232827867336398783/100000000000000000000 : ℝ) := by
    have hpowers : (25407/100000 : ℝ)^4531 ≤ (232827867336398783/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25407 : ℕ)^4531*100000000000000000000^1024 ≤ 232827867336398783^1024*100000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25407 100000 232827867336398783 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25407/100000 : ℝ)) (X := (232827867336398783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (625000197683406929/625000000000000000 : ℝ) ≤ (2500000178704731/2500000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (625000197683406929/625000000000000000 : ℝ)^1024 ≤ (2500000178704731/2500000000000000 : ℝ)^4531 := by
      have hnat : (625000197683406929 : ℕ)^1024*2500000000000000^4531 ≤ 2500000178704731^4531*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625000197683406929 625000000000000000 2500000178704731 2500000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000178704731/2500000000000000 : ℝ)) (X := (625000197683406929/625000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100232843682008953103/100000000000000000000 : ℝ) ≤ (10005257501062531/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (100232843682008953103/100000000000000000000 : ℝ)^1024 ≤ (10005257501062531/10000000000000000 : ℝ)^4531 := by
      have hnat : (100232843682008953103 : ℕ)^1024*10000000000000000^4531 ≤ 10005257501062531^4531*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100232843682008953103 100000000000000000000 10005257501062531 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005257501062531/10000000000000000 : ℝ)) (X := (100232843682008953103/100000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50232827867336398783/50000000000000000000 : ℝ) ≤ (5005257143653069/5000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50232827867336398783/50000000000000000000 : ℝ)^1024 ≤ (5005257143653069/5000000000000000 : ℝ)^4531 := by
      have hnat : (50232827867336398783 : ℕ)^1024*5000000000000000^4531 ≤ 5005257143653069^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50232827867336398783 50000000000000000000 5005257143653069 5000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005257143653069/5000000000000000 : ℝ)) (X := (50232827867336398783/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(197683406929/1250000000000000000 : ℝ) ≤ ((18749957055922281443/18752500000000000000 : ℝ)+2*(5256786243607/2250300000000000 : ℝ)*(363/12500 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (18749957055922281443/18752500000000000000 : ℝ)+2*(5256786243607/2250300000000000 : ℝ)*(363/12500 : ℝ)=(2500000178704731/2500000000000000 : ℝ) by norm_num, show 1+2*(197683406929/1250000000000000000 : ℝ)=(625000197683406929/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(232827867336398783/100000000000000000000 : ℝ)+(197683406929/1250000000000000000 : ℝ) ≤ ((18749957055922281443/18752500000000000000 : ℝ)+(5256786243607/2250300000000000 : ℝ)*((25407/100000 : ℝ)+(363/12500 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (18749957055922281443/18752500000000000000 : ℝ)+(5256786243607/2250300000000000 : ℝ)*((25407/100000 : ℝ)+(363/12500 : ℝ))=(10005257501062531/10000000000000000 : ℝ) by norm_num, show 1+(232827867336398783/100000000000000000000 : ℝ)+(197683406929/1250000000000000000 : ℝ)=(100232843682008953103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(232827867336398783/100000000000000000000 : ℝ) ≤ ((18749957055922281443/18752500000000000000 : ℝ)+2*(5256786243607/2250300000000000 : ℝ)*(25407/100000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (18749957055922281443/18752500000000000000 : ℝ)+2*(5256786243607/2250300000000000 : ℝ)*(25407/100000 : ℝ)=(5005257143653069/5000000000000000 : ℝ) by norm_num, show 1+2*(232827867336398783/100000000000000000000 : ℝ)=(50232827867336398783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18749957055922281443/18752500000000000000 : ℝ)*(X 1 0+X 2 0)+(5256786243607/2250300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (363/12500 : ℝ)) (hi := (25407/100000 : ℝ)) (c := (18749957055922281443/18752500000000000000 : ℝ)) (alpha := (5256786243607/2250300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18749957055922281443/18752500000000000000 : ℝ)*(X 0 1+X 2 1)+(5256786243607/2250300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (363/12500 : ℝ)) (hi := (25407/100000 : ℝ)) (c := (18749957055922281443/18752500000000000000 : ℝ)) (alpha := (5256786243607/2250300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18749957055922281443/18752500000000000000 : ℝ)*(X 0 2+X 1 2)+(5256786243607/2250300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (363/12500 : ℝ)) (hi := (25407/100000 : ℝ)) (c := (18749957055922281443/18752500000000000000 : ℝ)) (alpha := (5256786243607/2250300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5723737/31250000 : ℝ)*X 0 0+(173955033/312500000 : ℝ)*X 0 1+(5101749571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5385535353/10000000000 : ℝ)*X 1 0+(-207616761/1000000000 : ℝ)*X 1 1+(5101748943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5385534857/10000000000 : ℝ)*X 2 0+(5101749473/10000000000 : ℝ)*X 2 1+(-259520947/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530927631/1250000000 : ℝ)*X 0 0+(936474271/2500000000 : ℝ)*X 0 1+(4804355123/10000000000 : ℝ)*X 0 2+(530927631/1250000000 : ℝ)*X 1 0+(936474271/2500000000 : ℝ)*X 1 1+(4804355123/10000000000 : ℝ)*X 1 2+(530927631/1250000000 : ℝ)*X 2 0+(936474271/2500000000 : ℝ)*X 2 1+(4804355123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-183188663/1000000000 : ℝ)*X 0 0+(1276726031/2500000000 : ℝ)*X 0 1+(5561324309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263018677/10000000000 : ℝ)*X 1 0+(-1616592421/10000000000 : ℝ)*X 1 1+(5561324437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657877303/1250000000 : ℝ)*X 2 0+(1390331143/2500000000 : ℝ)*X 2 1+(-202074073/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2124041909/5000000000 : ℝ)*X 0 0+(4792617159/10000000000 : ℝ)*X 0 1+(939455409/2500000000 : ℝ)*X 0 2+(2124041909/5000000000 : ℝ)*X 1 0+(4792617159/10000000000 : ℝ)*X 1 1+(939455409/2500000000 : ℝ)*X 1 2+(2124041909/5000000000 : ℝ)*X 2 0+(4792617159/10000000000 : ℝ)*X 2 1+(939455409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3600186148635494924134437089/937625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (920843567/100000000000000 : ℝ)*(base19) + (687629279/100000000000000 : ℝ)*(base23) + (65174209/100000000000000 : ℝ)*(upper3) + (9443949/50000000000000 : ℝ)*(upper4) + (8111339/50000000000000 : ℝ)*(upper5) + (1548099100852559/100000000000000 : ℝ)*(major0) + (1548099100852559/100000000000000 : ℝ)*(major1) + (1548099100852559/100000000000000 : ℝ)*(major2) + (2151416217670157/100000000000000 : ℝ)*(sp0) + (1075710376683431/50000000000000 : ℝ)*(sp1) + (2151420986581149/100000000000000 : ℝ)*(sp2) + (944773412009747/100000000000000 : ℝ)*(sp3) + (5456540271/100000000000000 : ℝ)*(sp4) + (1493747691/50000000000000 : ℝ)*(sp7) + (94477639950513/10000000000000 : ℝ)*(f.failure) + (537855418552607/25000000000000 : ℝ)*(f.sum) + (31876826280517/112515000000000000000000000000 : ℝ)*base66 + (30695397793530612911/5625750000000000000000000000000000 : ℝ)*base67 + (16984047961652862911/5625750000000000000000000000000000 : ℝ)*base69 + (3475040547521387089/5625750000000000000000000000000000 : ℝ)*base72 + (723825901950323/112515000000000000000000000000 : ℝ)*base73 + (59839655283207137089/5625750000000000000000000000000000 : ℝ)*base76 + (7107341709298362911/5625750000000000000000000000000000 : ℝ)*base77 + (35022156037094862911/5625750000000000000000000000000000 : ℝ)*base79 + (121870842833839/56257500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5227583/500000000000000000000 : ℝ)*base89 + (5227583/500000000000000000000 : ℝ)*base91 + (5227583/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29543555604894595331349/9376250000000000000000000000 : ℝ) := by norm_num
    linear_combination (671745849/100000000000000 : ℝ)*(base19) + (317767059/50000000000000 : ℝ)*(base23) + (47464583/50000000000000 : ℝ)*(upper3) + (16463631/50000000000000 : ℝ)*(lower4) + (18880551/100000000000000 : ℝ)*(upper5) + (1583489799892981/100000000000000 : ℝ)*(major0) + (1583489799892981/100000000000000 : ℝ)*(major1) + (1583489799892981/100000000000000 : ℝ)*(major2) + (39337383/781250000000 : ℝ)*(sp1) + (533635639/10000000000000 : ℝ)*(sp2) + (2200604802740627/100000000000000 : ℝ)*(sp4) + (1100299547904877/50000000000000 : ℝ)*(sp5) + (1100299415425059/50000000000000 : ℝ)*(sp6) + (48318734600779/5000000000000 : ℝ)*(sp7) + (48318734600779/5000000000000 : ℝ)*(f.failure) + (2200604802740627/100000000000000 : ℝ)*(f.sum) + (3468381963983/112515000000000000000000000000 : ℝ)*base66 + (8274190042377570251/5625750000000000000000000000000000 : ℝ)*base68 + (15100518157493820251/5625750000000000000000000000000000 : ℝ)*base70 + (14547072326429070251/5625750000000000000000000000000000 : ℝ)*base72 + (386066943854723/112515000000000000000000000000 : ℝ)*base74 + (16023457725840929749/5625750000000000000000000000000000 : ℝ)*base75 + (13877978432571929749/5625750000000000000000000000000000 : ℝ)*base77 + (54866211329208929749/5625750000000000000000000000000000 : ℝ)*base79 + (415001659277453/112515000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (904411/250000000000000000000 : ℝ)*base90 + (904411/250000000000000000000 : ℝ)*base92 + (904411/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1518_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25407/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2109/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4567/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1518_s2_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46385859/250000000 : ℝ)*x 0 + (1364005643/2500000000 : ℝ)*x 1 + (2598418523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46385859/250000000 : ℝ)^4533 ≤ (11349131644359/100000000000000 : ℝ)^3509 := by
    have hnat : (46385859 : ℕ)^4533*100000000000000^3509 ≤ 11349131644359^3509*250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46385859 250000000 11349131644359 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364005643/2500000000 : ℝ)^4533 ≤ (45718406779321/100000000000000 : ℝ)^3509 := by
    have hnat : (1364005643 : ℕ)^4533*100000000000000^3509 ≤ 45718406779321^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364005643 2500000000 45718406779321 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598418523/5000000000 : ℝ)^4533 ≤ (21466230782261/50000000000000 : ℝ)^3509 := by
    have hnat : (2598418523 : ℕ)^4533*50000000000000^3509 ≤ 21466230782261^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598418523 5000000000 21466230782261 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46385859/250000000 : ℝ), (1364005643/2500000000 : ℝ), (2598418523/5000000000 : ℝ)] ![(11349131644359/100000000000000 : ℝ), (45718406779321/100000000000000 : ℝ), (21466230782261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46385859/250000000 : ℝ)|^4533 ≤ (11349131644359/100000000000000 : ℝ)^3509
        have hw : |(-46385859/250000000 : ℝ)|=(46385859/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364005643/2500000000 : ℝ)|^4533 ≤ (45718406779321/100000000000000 : ℝ)^3509
        have hw : |(1364005643/2500000000 : ℝ)|=(1364005643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598418523/5000000000 : ℝ)|^4533 ≤ (21466230782261/50000000000000 : ℝ)^3509
        have hw : |(2598418523/5000000000 : ℝ)|=(2598418523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267869817/500000000 : ℝ)*x 0 + (-1988811421/10000000000 : ℝ)*x 1 + (5196837053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267869817/500000000 : ℝ)^4533 ≤ (8930726383347/20000000000000 : ℝ)^3509 := by
    have hnat : (267869817 : ℕ)^4533*20000000000000^3509 ≤ 8930726383347^3509*500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267869817 500000000 8930726383347 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988811421/10000000000 : ℝ)^4533 ≤ (1241390643109/10000000000000 : ℝ)^3509 := by
    have hnat : (1988811421 : ℕ)^4533*10000000000000^3509 ≤ 1241390643109^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988811421 10000000000 1241390643109 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196837053/10000000000 : ℝ)^4533 ≤ (42932461639227/100000000000000 : ℝ)^3509 := by
    have hnat : (5196837053 : ℕ)^4533*100000000000000^3509 ≤ 42932461639227^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196837053 10000000000 42932461639227 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267869817/500000000 : ℝ), (-1988811421/10000000000 : ℝ), (5196837053/10000000000 : ℝ)] ![(8930726383347/20000000000000 : ℝ), (1241390643109/10000000000000 : ℝ), (42932461639227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267869817/500000000 : ℝ)|^4533 ≤ (8930726383347/20000000000000 : ℝ)^3509
        have hw : |(267869817/500000000 : ℝ)|=(267869817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988811421/10000000000 : ℝ)|^4533 ≤ (1241390643109/10000000000000 : ℝ)^3509
        have hw : |(-1988811421/10000000000 : ℝ)|=(1988811421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196837053/10000000000 : ℝ)|^4533 ≤ (42932461639227/100000000000000 : ℝ)^3509
        have hw : |(5196837053/10000000000 : ℝ)|=(5196837053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678698113/5000000000 : ℝ)*x 0 + (1299209279/2500000000 : ℝ)*x 1 + (-198881149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678698113/5000000000 : ℝ)^4533 ≤ (44653630689267/100000000000000 : ℝ)^3509 := by
    have hnat : (2678698113 : ℕ)^4533*100000000000000^3509 ≤ 44653630689267^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678698113 5000000000 44653630689267 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299209279/2500000000 : ℝ)^4533 ≤ (42932462311567/100000000000000 : ℝ)^3509 := by
    have hnat : (1299209279 : ℕ)^4533*100000000000000^3509 ≤ 42932462311567^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299209279 2500000000 42932462311567 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198881149/1000000000 : ℝ)^4533 ≤ (12413906987463/100000000000000 : ℝ)^3509 := by
    have hnat : (198881149 : ℕ)^4533*100000000000000^3509 ≤ 12413906987463^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198881149 1000000000 12413906987463 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678698113/5000000000 : ℝ), (1299209279/2500000000 : ℝ), (-198881149/1000000000 : ℝ)] ![(44653630689267/100000000000000 : ℝ), (42932462311567/100000000000000 : ℝ), (12413906987463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678698113/5000000000 : ℝ)|^4533 ≤ (44653630689267/100000000000000 : ℝ)^3509
        have hw : |(2678698113/5000000000 : ℝ)|=(2678698113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299209279/2500000000 : ℝ)|^4533 ≤ (42932462311567/100000000000000 : ℝ)^3509
        have hw : |(1299209279/2500000000 : ℝ)|=(1299209279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198881149/1000000000 : ℝ)|^4533 ≤ (12413906987463/100000000000000 : ℝ)^3509
        have hw : |(-198881149/1000000000 : ℝ)|=(198881149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170582117/400000000 : ℝ)*x 0 + (31078637/78125000 : ℝ)*x 1 + (4568275821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170582117/400000000 : ℝ)^4533 ≤ (33255448858021/100000000000000 : ℝ)^3509 := by
    have hnat : (170582117 : ℕ)^4533*100000000000000^3509 ≤ 33255448858021^3509*400000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170582117 400000000 33255448858021 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31078637/78125000 : ℝ)^4533 ≤ (7599548533261/25000000000000 : ℝ)^3509 := by
    have hnat : (31078637 : ℕ)^4533*25000000000000^3509 ≤ 7599548533261^3509*78125000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31078637 78125000 7599548533261 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4568275821/10000000000 : ℝ)^4533 ≤ (18173178498943/50000000000000 : ℝ)^3509 := by
    have hnat : (4568275821 : ℕ)^4533*50000000000000^3509 ≤ 18173178498943^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568275821 10000000000 18173178498943 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170582117/400000000 : ℝ), (31078637/78125000 : ℝ), (4568275821/10000000000 : ℝ)] ![(33255448858021/100000000000000 : ℝ), (7599548533261/25000000000000 : ℝ), (18173178498943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170582117/400000000 : ℝ)|^4533 ≤ (33255448858021/100000000000000 : ℝ)^3509
        have hw : |(170582117/400000000 : ℝ)|=(170582117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31078637/78125000 : ℝ)|^4533 ≤ (7599548533261/25000000000000 : ℝ)^3509
        have hw : |(31078637/78125000 : ℝ)|=(31078637/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4568275821/10000000000 : ℝ)|^4533 ≤ (18173178498943/50000000000000 : ℝ)^3509
        have hw : |(4568275821/10000000000 : ℝ)|=(4568275821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92774357/500000000 : ℝ)*x 0 + (1299611389/2500000000 : ℝ)*x 1 + (1363599519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92774357/500000000 : ℝ)^4533 ≤ (5674774348357/50000000000000 : ℝ)^3509 := by
    have hnat : (92774357 : ℕ)^4533*50000000000000^3509 ≤ 5674774348357^3509*500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92774357 500000000 5674774348357 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299611389/2500000000 : ℝ)^4533 ≤ (42949628485909/100000000000000 : ℝ)^3509 := by
    have hnat : (1299611389 : ℕ)^4533*100000000000000^3509 ≤ 42949628485909^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299611389 2500000000 42949628485909 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363599519/2500000000 : ℝ)^4533 ≤ (5712602850543/12500000000000 : ℝ)^3509 := by
    have hnat : (1363599519 : ℕ)^4533*12500000000000^3509 ≤ 5712602850543^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363599519 2500000000 5712602850543 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92774357/500000000 : ℝ), (1299611389/2500000000 : ℝ), (1363599519/2500000000 : ℝ)] ![(5674774348357/50000000000000 : ℝ), (42949628485909/100000000000000 : ℝ), (5712602850543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92774357/500000000 : ℝ)|^4533 ≤ (5674774348357/50000000000000 : ℝ)^3509
        have hw : |(-92774357/500000000 : ℝ)|=(92774357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299611389/2500000000 : ℝ)|^4533 ≤ (42949628485909/100000000000000 : ℝ)^3509
        have hw : |(1299611389/2500000000 : ℝ)|=(1299611389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363599519/2500000000 : ℝ)|^4533 ≤ (5712602850543/12500000000000 : ℝ)^3509
        have hw : |(1363599519/2500000000 : ℝ)|=(1363599519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289281417/10000000000 : ℝ)*x 0 + (-346250427/2000000000 : ℝ)*x 1 + (681799413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289281417/10000000000 : ℝ)^4533 ≤ (8784317047739/20000000000000 : ℝ)^3509 := by
    have hnat : (5289281417 : ℕ)^4533*20000000000000^3509 ≤ 8784317047739^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289281417 10000000000 8784317047739 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346250427/2000000000 : ℝ)^4533 ≤ (2075524389201/20000000000000 : ℝ)^3509 := by
    have hnat : (346250427 : ℕ)^4533*20000000000000^3509 ≤ 2075524389201^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346250427 2000000000 2075524389201 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681799413/1250000000 : ℝ)^4533 ≤ (11425198200197/25000000000000 : ℝ)^3509 := by
    have hnat : (681799413 : ℕ)^4533*25000000000000^3509 ≤ 11425198200197^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681799413 1250000000 11425198200197 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289281417/10000000000 : ℝ), (-346250427/2000000000 : ℝ), (681799413/1250000000 : ℝ)] ![(8784317047739/20000000000000 : ℝ), (2075524389201/20000000000000 : ℝ), (11425198200197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289281417/10000000000 : ℝ)|^4533 ≤ (8784317047739/20000000000000 : ℝ)^3509
        have hw : |(5289281417/10000000000 : ℝ)|=(5289281417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346250427/2000000000 : ℝ)|^4533 ≤ (2075524389201/20000000000000 : ℝ)^3509
        have hw : |(-346250427/2000000000 : ℝ)|=(346250427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681799413/1250000000 : ℝ)|^4533 ≤ (11425198200197/25000000000000 : ℝ)^3509
        have hw : |(681799413/1250000000 : ℝ)|=(681799413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289282039/10000000000 : ℝ)*x 0 + (5454395573/10000000000 : ℝ)*x 1 + (-865625449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289282039/10000000000 : ℝ)^4533 ≤ (10980397977743/25000000000000 : ℝ)^3509 := by
    have hnat : (5289282039 : ℕ)^4533*25000000000000^3509 ≤ 10980397977743^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289282039 10000000000 10980397977743 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454395573/10000000000 : ℝ)^4533 ≤ (11425198928097/25000000000000 : ℝ)^3509 := by
    have hnat : (5454395573 : ℕ)^4533*25000000000000^3509 ≤ 11425198928097^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454395573 10000000000 11425198928097 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865625449/5000000000 : ℝ)^4533 ≤ (259440309181/2500000000000 : ℝ)^3509 := by
    have hnat : (865625449 : ℕ)^4533*2500000000000^3509 ≤ 259440309181^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865625449 5000000000 259440309181 2500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289282039/10000000000 : ℝ), (5454395573/10000000000 : ℝ), (-865625449/5000000000 : ℝ)] ![(10980397977743/25000000000000 : ℝ), (11425198928097/25000000000000 : ℝ), (259440309181/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289282039/10000000000 : ℝ)|^4533 ≤ (10980397977743/25000000000000 : ℝ)^3509
        have hw : |(5289282039/10000000000 : ℝ)|=(5289282039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454395573/10000000000 : ℝ)|^4533 ≤ (11425198928097/25000000000000 : ℝ)^3509
        have hw : |(5454395573/10000000000 : ℝ)|=(5454395573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-865625449/5000000000 : ℝ)|^4533 ≤ (259440309181/2500000000000 : ℝ)^3509
        have hw : |(-865625449/5000000000 : ℝ)|=(865625449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426466673/1000000000 : ℝ)*x 0 + (114115171/250000000 : ℝ)*x 1 + (31107567/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426466673/1000000000 : ℝ)^4533 ≤ (33256595306891/100000000000000 : ℝ)^3509 := by
    have hnat : (426466673 : ℕ)^4533*100000000000000^3509 ≤ 33256595306891^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426466673 1000000000 33256595306891 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114115171/250000000 : ℝ)^4533 ≤ (18154325715371/50000000000000 : ℝ)^3509 := by
    have hnat : (114115171 : ℕ)^4533*50000000000000^3509 ≤ 18154325715371^3509*250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114115171 250000000 18154325715371 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31107567/78125000 : ℝ)^4533 ≤ (30434753239703/100000000000000 : ℝ)^3509 := by
    have hnat : (31107567 : ℕ)^4533*100000000000000^3509 ≤ 30434753239703^3509*78125000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31107567 78125000 30434753239703 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426466673/1000000000 : ℝ), (114115171/250000000 : ℝ), (31107567/78125000 : ℝ)] ![(33256595306891/100000000000000 : ℝ), (18154325715371/50000000000000 : ℝ), (30434753239703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426466673/1000000000 : ℝ)|^4533 ≤ (33256595306891/100000000000000 : ℝ)^3509
        have hw : |(426466673/1000000000 : ℝ)|=(426466673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114115171/250000000 : ℝ)|^4533 ≤ (18154325715371/50000000000000 : ℝ)^3509
        have hw : |(114115171/250000000 : ℝ)|=(114115171/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31107567/78125000 : ℝ)|^4533 ≤ (30434753239703/100000000000000 : ℝ)^3509
        have hw : |(31107567/78125000 : ℝ)|=(31107567/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_8 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4025033/5000000000 : ℝ)*x 0 + (584675157/1000000000 : ℝ)*x 1 + (5847394711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4025033/5000000000 : ℝ)^4533 ≤ (10065761637/100000000000000 : ℝ)^3509 := by
    have hnat : (4025033 : ℕ)^4533*100000000000000^3509 ≤ 10065761637^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025033 5000000000 10065761637 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584675157/1000000000 : ℝ)^4533 ≤ (9998283033013/20000000000000 : ℝ)^3509 := by
    have hnat : (584675157 : ℕ)^4533*20000000000000^3509 ≤ 9998283033013^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584675157 1000000000 9998283033013 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5847394711/10000000000 : ℝ)^4533 ≤ (49998519056369/100000000000000 : ℝ)^3509 := by
    have hnat : (5847394711 : ℕ)^4533*100000000000000^3509 ≤ 49998519056369^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847394711 10000000000 49998519056369 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4025033/5000000000 : ℝ), (584675157/1000000000 : ℝ), (5847394711/10000000000 : ℝ)] ![(10065761637/100000000000000 : ℝ), (9998283033013/20000000000000 : ℝ), (49998519056369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4025033/5000000000 : ℝ)|^4533 ≤ (10065761637/100000000000000 : ℝ)^3509
        have hw : |(-4025033/5000000000 : ℝ)|=(4025033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(584675157/1000000000 : ℝ)|^4533 ≤ (9998283033013/20000000000000 : ℝ)^3509
        have hw : |(584675157/1000000000 : ℝ)|=(584675157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5847394711/10000000000 : ℝ)|^4533 ≤ (49998519056369/100000000000000 : ℝ)^3509
        have hw : |(5847394711/10000000000 : ℝ)|=(5847394711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_9 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (69240953/625000000 : ℝ)*x 0 + (-994685401/2500000000 : ℝ)*x 1 + (3529388849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69240953/625000000 : ℝ)^4533 ≤ (1457414469443/25000000000000 : ℝ)^3509 := by
    have hnat : (69240953 : ℕ)^4533*25000000000000^3509 ≤ 1457414469443^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69240953 625000000 1457414469443 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994685401/2500000000 : ℝ)^4533 ≤ (30404868027749/100000000000000 : ℝ)^3509 := by
    have hnat : (994685401 : ℕ)^4533*100000000000000^3509 ≤ 30404868027749^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994685401 2500000000 30404868027749 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3529388849/5000000000 : ℝ)^4533 ≤ (6376547408521/10000000000000 : ℝ)^3509 := by
    have hnat : (3529388849 : ℕ)^4533*10000000000000^3509 ≤ 6376547408521^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3529388849 5000000000 6376547408521 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(69240953/625000000 : ℝ), (-994685401/2500000000 : ℝ), (3529388849/5000000000 : ℝ)] ![(1457414469443/25000000000000 : ℝ), (30404868027749/100000000000000 : ℝ), (6376547408521/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(69240953/625000000 : ℝ)|^4533 ≤ (1457414469443/25000000000000 : ℝ)^3509
        have hw : |(69240953/625000000 : ℝ)|=(69240953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994685401/2500000000 : ℝ)|^4533 ≤ (30404868027749/100000000000000 : ℝ)^3509
        have hw : |(-994685401/2500000000 : ℝ)|=(994685401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3529388849/5000000000 : ℝ)|^4533 ≤ (6376547408521/10000000000000 : ℝ)^3509
        have hw : |(3529388849/5000000000 : ℝ)|=(3529388849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_10 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1107862547/10000000000 : ℝ)*x 0 + (282351739/400000000 : ℝ)*x 1 + (-497339741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107862547/10000000000 : ℝ)^4533 ≤ (2914853747139/50000000000000 : ℝ)^3509 := by
    have hnat : (1107862547 : ℕ)^4533*50000000000000^3509 ≤ 2914853747139^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107862547 10000000000 2914853747139 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282351739/400000000 : ℝ)^4533 ≤ (12753131639519/20000000000000 : ℝ)^3509 := by
    have hnat : (282351739 : ℕ)^4533*20000000000000^3509 ≤ 12753131639519^3509*400000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282351739 400000000 12753131639519 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497339741/1250000000 : ℝ)^4533 ≤ (3040463430139/10000000000000 : ℝ)^3509 := by
    have hnat : (497339741 : ℕ)^4533*10000000000000^3509 ≤ 3040463430139^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497339741 1250000000 3040463430139 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1107862547/10000000000 : ℝ), (282351739/400000000 : ℝ), (-497339741/1250000000 : ℝ)] ![(2914853747139/50000000000000 : ℝ), (12753131639519/20000000000000 : ℝ), (3040463430139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1107862547/10000000000 : ℝ)|^4533 ≤ (2914853747139/50000000000000 : ℝ)^3509
        have hw : |(1107862547/10000000000 : ℝ)|=(1107862547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282351739/400000000 : ℝ)|^4533 ≤ (12753131639519/20000000000000 : ℝ)^3509
        have hw : |(282351739/400000000 : ℝ)|=(282351739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497339741/1250000000 : ℝ)|^4533 ≤ (3040463430139/10000000000000 : ℝ)^3509
        have hw : |(-497339741/1250000000 : ℝ)|=(497339741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s2_11 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1646539483/10000000000 : ℝ)*x 0 + (727802711/1250000000 : ℝ)*x 1 + (4972235769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1646539483/10000000000 : ℝ)^4533 ≤ (9726384314861/100000000000000 : ℝ)^3509 := by
    have hnat : (1646539483 : ℕ)^4533*100000000000000^3509 ≤ 9726384314861^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646539483 10000000000 9726384314861 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727802711/1250000000 : ℝ)^4533 ≤ (9944568833511/20000000000000 : ℝ)^3509 := by
    have hnat : (727802711 : ℕ)^4533*20000000000000^3509 ≤ 9944568833511^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727802711 1250000000 9944568833511 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4972235769/10000000000 : ℝ)^4533 ≤ (40550771509611/100000000000000 : ℝ)^3509 := by
    have hnat : (4972235769 : ℕ)^4533*100000000000000^3509 ≤ 40550771509611^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4972235769 10000000000 40550771509611 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1646539483/10000000000 : ℝ), (727802711/1250000000 : ℝ), (4972235769/10000000000 : ℝ)] ![(9726384314861/100000000000000 : ℝ), (9944568833511/20000000000000 : ℝ), (40550771509611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1646539483/10000000000 : ℝ)|^4533 ≤ (9726384314861/100000000000000 : ℝ)^3509
        have hw : |(1646539483/10000000000 : ℝ)|=(1646539483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(727802711/1250000000 : ℝ)|^4533 ≤ (9944568833511/20000000000000 : ℝ)^3509
        have hw : |(727802711/1250000000 : ℝ)|=(727802711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4972235769/10000000000 : ℝ)|^4533 ≤ (40550771509611/100000000000000 : ℝ)^3509
        have hw : |(4972235769/10000000000 : ℝ)|=(4972235769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4567/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2109/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7987/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4567/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2109/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4567/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2109/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4567/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2109/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4567/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2109/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4567/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2109/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4567/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2109/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2109/25000 : ℝ) ^ (4531/1024 : ℝ) ≤ (1771593449992467/100000000000000000000 : ℝ) := by
    have hpowers : (2109/25000 : ℝ)^4531 ≤ (1771593449992467/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2109 : ℕ)^4531*100000000000000000000^1024 ≤ 1771593449992467^1024*25000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2109 25000 1771593449992467 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2109/25000 : ℝ)) (X := (1771593449992467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4567/25000 : ℝ) ^ (4531/1024 : ℝ) ≤ (54091233964402783/100000000000000000000 : ℝ) := by
    have hpowers : (4567/25000 : ℝ)^4531 ≤ (54091233964402783/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4567 : ℕ)^4531*100000000000000000000^1024 ≤ 54091233964402783^1024*25000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4567 25000 54091233964402783 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4567/25000 : ℝ)) (X := (54091233964402783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001771593449992467/50000000000000000000 : ℝ) ≤ (5000040037228381/5000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50001771593449992467/50000000000000000000 : ℝ)^1024 ≤ (5000040037228381/5000000000000000 : ℝ)^4531 := by
      have hnat : (50001771593449992467 : ℕ)^1024*5000000000000000^4531 ≤ 5000040037228381^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001771593449992467 50000000000000000000 5000040037228381 5000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000040037228381/5000000000000000 : ℝ)) (X := (50001771593449992467/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (400223451309657581/400000000000000000 : ℝ) ≤ (10001262219654637/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (400223451309657581/400000000000000000 : ℝ)^1024 ≤ (10001262219654637/10000000000000000 : ℝ)^4531 := by
      have hnat : (400223451309657581 : ℕ)^1024*10000000000000000^4531 ≤ 10001262219654637^4531*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400223451309657581 400000000000000000 10001262219654637 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001262219654637/10000000000000000 : ℝ)) (X := (400223451309657581/400000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054091233964402783/50000000000000000000 : ℝ) ≤ (312576386401641/312500000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50054091233964402783/50000000000000000000 : ℝ)^1024 ≤ (312576386401641/312500000000000 : ℝ)^4531 := by
      have hnat : (50054091233964402783 : ℕ)^1024*312500000000000^4531 ≤ 312576386401641^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054091233964402783 50000000000000000000 312576386401641 312500000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312576386401641/312500000000000 : ℝ)) (X := (50054091233964402783/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1771593449992467/100000000000000000000 : ℝ) ≤ ((12287605267285042123/12290000000000000000 : ℝ)+2*(9457161583/7865600000000 : ℝ)*(2109/25000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (12287605267285042123/12290000000000000000 : ℝ)+2*(9457161583/7865600000000 : ℝ)*(2109/25000 : ℝ)=(5000040037228381/5000000000000000 : ℝ) by norm_num, show 1+2*(1771593449992467/100000000000000000000 : ℝ)=(50001771593449992467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54091233964402783/100000000000000000000 : ℝ)+(1771593449992467/100000000000000000000 : ℝ) ≤ ((12287605267285042123/12290000000000000000 : ℝ)+(9457161583/7865600000000 : ℝ)*((4567/25000 : ℝ)+(2109/25000 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (12287605267285042123/12290000000000000000 : ℝ)+(9457161583/7865600000000 : ℝ)*((4567/25000 : ℝ)+(2109/25000 : ℝ))=(10001262219654637/10000000000000000 : ℝ) by norm_num, show 1+(54091233964402783/100000000000000000000 : ℝ)+(1771593449992467/100000000000000000000 : ℝ)=(400223451309657581/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54091233964402783/100000000000000000000 : ℝ) ≤ ((12287605267285042123/12290000000000000000 : ℝ)+2*(9457161583/7865600000000 : ℝ)*(4567/25000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (12287605267285042123/12290000000000000000 : ℝ)+2*(9457161583/7865600000000 : ℝ)*(4567/25000 : ℝ)=(312576386401641/312500000000000 : ℝ) by norm_num, show 1+2*(54091233964402783/100000000000000000000 : ℝ)=(50054091233964402783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12287605267285042123/12290000000000000000 : ℝ)*(X 1 0+X 2 0)+(9457161583/7865600000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (2109/25000 : ℝ)) (hi := (4567/25000 : ℝ)) (c := (12287605267285042123/12290000000000000000 : ℝ)) (alpha := (9457161583/7865600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12287605267285042123/12290000000000000000 : ℝ)*(X 0 1+X 2 1)+(9457161583/7865600000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (2109/25000 : ℝ)) (hi := (4567/25000 : ℝ)) (c := (12287605267285042123/12290000000000000000 : ℝ)) (alpha := (9457161583/7865600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12287605267285042123/12290000000000000000 : ℝ)*(X 0 2+X 1 2)+(9457161583/7865600000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (2109/25000 : ℝ)) (hi := (4567/25000 : ℝ)) (c := (12287605267285042123/12290000000000000000 : ℝ)) (alpha := (9457161583/7865600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-46385859/250000000 : ℝ)*X 0 0+(1364005643/2500000000 : ℝ)*X 0 1+(2598418523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267869817/500000000 : ℝ)*X 1 0+(-1988811421/10000000000 : ℝ)*X 1 1+(5196837053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678698113/5000000000 : ℝ)*X 2 0+(1299209279/2500000000 : ℝ)*X 2 1+(-198881149/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((170582117/400000000 : ℝ)*X 0 0+(31078637/78125000 : ℝ)*X 0 1+(4568275821/10000000000 : ℝ)*X 0 2+(170582117/400000000 : ℝ)*X 1 0+(31078637/78125000 : ℝ)*X 1 1+(4568275821/10000000000 : ℝ)*X 1 2+(170582117/400000000 : ℝ)*X 2 0+(31078637/78125000 : ℝ)*X 2 1+(4568275821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92774357/500000000 : ℝ)*X 0 0+(1299611389/2500000000 : ℝ)*X 0 1+(1363599519/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289281417/10000000000 : ℝ)*X 1 0+(-346250427/2000000000 : ℝ)*X 1 1+(681799413/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289282039/10000000000 : ℝ)*X 2 0+(5454395573/10000000000 : ℝ)*X 2 1+(-865625449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((426466673/1000000000 : ℝ)*X 0 0+(114115171/250000000 : ℝ)*X 0 1+(31107567/78125000 : ℝ)*X 0 2+(426466673/1000000000 : ℝ)*X 1 0+(114115171/250000000 : ℝ)*X 1 1+(31107567/78125000 : ℝ)*X 1 2+(426466673/1000000000 : ℝ)*X 2 0+(114115171/250000000 : ℝ)*X 2 1+(31107567/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-4025033/5000000000 : ℝ)*X 0 0+(584675157/1000000000 : ℝ)*X 0 1+(5847394711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((69240953/625000000 : ℝ)*X 1 0+(-994685401/2500000000 : ℝ)*X 1 1+(3529388849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1107862547/10000000000 : ℝ)*X 2 0+(282351739/400000000 : ℝ)*X 2 1+(-497339741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1646539483/10000000000 : ℝ)*X 0 0+(727802711/1250000000 : ℝ)*X 0 1+(4972235769/10000000000 : ℝ)*X 0 2+(1646539483/10000000000 : ℝ)*X 1 0+(727802711/1250000000 : ℝ)*X 1 1+(4972235769/10000000000 : ℝ)*X 1 2+(1646539483/10000000000 : ℝ)*X 2 0+(727802711/1250000000 : ℝ)*X 2 1+(4972235769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4305716858497663074090915447/614500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2776280983711863/100000000000000 : ℝ)*(major0) + (2776280983711863/100000000000000 : ℝ)*(major1) + (2776280983711863/100000000000000 : ℝ)*(major2) + (1929122027089189/50000000000000 : ℝ)*(sp0) + (96456158564283/2500000000000 : ℝ)*(sp1) + (3858246427269731/100000000000000 : ℝ)*(sp2) + (338862498890457/20000000000000 : ℝ)*(sp3) + (3748503579/100000000000000 : ℝ)*(sp4) + (207076519/12500000000000 : ℝ)*(sp5) + (837861019/50000000000000 : ℝ)*(sp6) + (724511363/100000000000000 : ℝ)*(sp8) + (528009849/100000000000000 : ℝ)*(sp9) + (424201551/100000000000000 : ℝ)*(sp10) + (356108021/50000000000000 : ℝ)*(sp11) + (1694313206668327/100000000000000 : ℝ)*(f.failure) + (96456213179833/2500000000000 : ℝ)*(f.sum) + (10093510520809/9832000000000000000000000000 : ℝ)*base65 + (466206569185132351/1229000000000000000000000000000000 : ℝ)*base68 + (1142232356616867649/1229000000000000000000000000000000 : ℝ)*base69 + (3957308812674132351/1229000000000000000000000000000000 : ℝ)*base72 + (4006353368477/1966400000000000000000000000 : ℝ)*base73 + (9685128948648132351/1229000000000000000000000000000000 : ℝ)*base76 + (4090330056595132351/1229000000000000000000000000000000 : ℝ)*base78 + (4148110499709867649/1229000000000000000000000000000000 : ℝ)*base79 + (6076922556087/9832000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20098857/5000000000000000000000 : ℝ)*base89 + (20098857/5000000000000000000000 : ℝ)*base91 + (20098857/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12546277440572433242031/1966400000000000000000000000 : ℝ) := by norm_num
    linear_combination (562281352707757/20000000000000 : ℝ)*(major0) + (562281352707757/20000000000000 : ℝ)*(major1) + (562281352707757/20000000000000 : ℝ)*(major2) + (40440944537/100000000000000 : ℝ)*(sp0) + (10484042541/100000000000000 : ℝ)*(sp2) + (3601155969/100000000000000 : ℝ)*(sp3) + (390701728885359/10000000000000 : ℝ)*(sp4) + (390706182116433/10000000000000 : ℝ)*(sp5) + (1953525292574141/50000000000000 : ℝ)*(sp6) + (343149230850893/20000000000000 : ℝ)*(sp7) + (720093137/12500000000000 : ℝ)*(sp8) + (417344723/25000000000000 : ℝ)*(sp9) + (1210676199/50000000000000 : ℝ)*(sp10) + (68446297/100000000000000 : ℝ)*(sp11) + (428937455964183/25000000000000 : ℝ)*(f.failure) + (1953531745271611/50000000000000 : ℝ)*(f.sum) + (6870614003067/1966400000000000000000000000 : ℝ)*base65 + (1485104604916664389/245800000000000000000000000000000 : ℝ)*base68 + (1031643507105464389/245800000000000000000000000000000 : ℝ)*base70 + (483441044923064389/245800000000000000000000000000000 : ℝ)*base72 + (901473707289/9832000000000000000000000000 : ℝ)*base74 + (614808676774135611/245800000000000000000000000000000 : ℝ)*base75 + (1736350698481735611/245800000000000000000000000000000 : ℝ)*base77 + (2248824890848935611/245800000000000000000000000000000 : ℝ)*base79 + (24410783075191/9832000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (18502553/1250000000000000000000 : ℝ)*base89 + (18502553/1250000000000000000000 : ℝ)*base91 + (18502553/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1518_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4567/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2109/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1518_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1518_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1518_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1518_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1518_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

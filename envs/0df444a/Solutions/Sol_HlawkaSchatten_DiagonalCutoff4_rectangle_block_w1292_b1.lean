-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1292_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:26.222471+00:00
-- url     : https://prove2.me/submissions/2eada0d4-ea5d-4968-8f68-0f83cd754a22

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
theorem support_rectangle_w1292_s3_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-417122913/2000000000 : ℝ)*x 0 + (5434072899/10000000000 : ℝ)*x 1 + (5225693759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417122913/2000000000 : ℝ)^1063 ≤ (507386081207/4000000000000 : ℝ)^807 := by
    have hnat : (417122913 : ℕ)^1063*4000000000000^807 ≤ 507386081207^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417122913 2000000000 507386081207 4000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434072899/10000000000 : ℝ)^1063 ≤ (11195431364583/25000000000000 : ℝ)^807 := by
    have hnat : (5434072899 : ℕ)^1063*25000000000000^807 ≤ 11195431364583^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434072899 10000000000 11195431364583 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225693759/10000000000 : ℝ)^1063 ≤ (42533622497697/100000000000000 : ℝ)^807 := by
    have hnat : (5225693759 : ℕ)^1063*100000000000000^807 ≤ 42533622497697^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225693759 10000000000 42533622497697 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417122913/2000000000 : ℝ), (5434072899/10000000000 : ℝ), (5225693759/10000000000 : ℝ)] ![(507386081207/4000000000000 : ℝ), (11195431364583/25000000000000 : ℝ), (42533622497697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417122913/2000000000 : ℝ)|^1063 ≤ (507386081207/4000000000000 : ℝ)^807
        have hw : |(-417122913/2000000000 : ℝ)|=(417122913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434072899/10000000000 : ℝ)|^1063 ≤ (11195431364583/25000000000000 : ℝ)^807
        have hw : |(5434072899/10000000000 : ℝ)|=(5434072899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225693759/10000000000 : ℝ)|^1063 ≤ (42533622497697/100000000000000 : ℝ)^807
        have hw : |(5225693759/10000000000 : ℝ)|=(5225693759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5354549759/10000000000 : ℝ)*x 0 + (-10961301/50000000 : ℝ)*x 1 + (209027753/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354549759/10000000000 : ℝ)^1063 ≤ (21960250862871/50000000000000 : ℝ)^807 := by
    have hnat : (5354549759 : ℕ)^1063*50000000000000^807 ≤ 21960250862871^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354549759 10000000000 21960250862871 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10961301/50000000 : ℝ)^1063 ≤ (13545875050141/100000000000000 : ℝ)^807 := by
    have hnat : (10961301 : ℕ)^1063*100000000000000^807 ≤ 13545875050141^807*50000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10961301 50000000 13545875050141 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209027753/400000000 : ℝ)^1063 ≤ (5316702900663/12500000000000 : ℝ)^807 := by
    have hnat : (209027753 : ℕ)^1063*12500000000000^807 ≤ 5316702900663^807*400000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209027753 400000000 5316702900663 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354549759/10000000000 : ℝ), (-10961301/50000000 : ℝ), (209027753/400000000 : ℝ)] ![(21960250862871/50000000000000 : ℝ), (13545875050141/100000000000000 : ℝ), (5316702900663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354549759/10000000000 : ℝ)|^1063 ≤ (21960250862871/50000000000000 : ℝ)^807
        have hw : |(5354549759/10000000000 : ℝ)|=(5354549759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10961301/50000000 : ℝ)|^1063 ≤ (13545875050141/100000000000000 : ℝ)^807
        have hw : |(-10961301/50000000 : ℝ)|=(10961301/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209027753/400000000 : ℝ)|^1063 ≤ (5316702900663/12500000000000 : ℝ)^807
        have hw : |(209027753/400000000 : ℝ)|=(209027753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2677274901/5000000000 : ℝ)*x 0 + (5225693589/10000000000 : ℝ)*x 1 + (-2192260453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677274901/5000000000 : ℝ)^1063 ≤ (8784100438067/20000000000000 : ℝ)^807 := by
    have hnat : (2677274901 : ℕ)^1063*20000000000000^807 ≤ 8784100438067^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677274901 5000000000 8784100438067 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225693589/10000000000 : ℝ)^1063 ≤ (42533620675073/100000000000000 : ℝ)^807 := by
    have hnat : (5225693589 : ℕ)^1063*100000000000000^807 ≤ 42533620675073^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225693589 10000000000 42533620675073 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192260453/10000000000 : ℝ)^1063 ≤ (6772938554663/50000000000000 : ℝ)^807 := by
    have hnat : (2192260453 : ℕ)^1063*50000000000000^807 ≤ 6772938554663^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192260453 10000000000 6772938554663 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677274901/5000000000 : ℝ), (5225693589/10000000000 : ℝ), (-2192260453/10000000000 : ℝ)] ![(8784100438067/20000000000000 : ℝ), (42533620675073/100000000000000 : ℝ), (6772938554663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677274901/5000000000 : ℝ)|^1063 ≤ (8784100438067/20000000000000 : ℝ)^807
        have hw : |(2677274901/5000000000 : ℝ)|=(2677274901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225693589/10000000000 : ℝ)|^1063 ≤ (42533620675073/100000000000000 : ℝ)^807
        have hw : |(5225693589/10000000000 : ℝ)|=(5225693589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192260453/10000000000 : ℝ)|^1063 ≤ (6772938554663/50000000000000 : ℝ)^807
        have hw : |(-2192260453/10000000000 : ℝ)|=(2192260453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4338448071/10000000000 : ℝ)*x 0 + (2064680623/5000000000 : ℝ)*x 1 + (1139407529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338448071/10000000000 : ℝ)^1063 ≤ (33288028001103/100000000000000 : ℝ)^807 := by
    have hnat : (4338448071 : ℕ)^1063*100000000000000^807 ≤ 33288028001103^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338448071 10000000000 33288028001103 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064680623/5000000000 : ℝ)^1063 ≤ (623823301519/2000000000000 : ℝ)^807 := by
    have hnat : (2064680623 : ℕ)^1063*2000000000000^807 ≤ 623823301519^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064680623 5000000000 623823301519 2000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139407529/2500000000 : ℝ)^1063 ≤ (35520806902627/100000000000000 : ℝ)^807 := by
    have hnat : (1139407529 : ℕ)^1063*100000000000000^807 ≤ 35520806902627^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139407529 2500000000 35520806902627 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338448071/10000000000 : ℝ), (2064680623/5000000000 : ℝ), (1139407529/2500000000 : ℝ)] ![(33288028001103/100000000000000 : ℝ), (623823301519/2000000000000 : ℝ), (35520806902627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338448071/10000000000 : ℝ)|^1063 ≤ (33288028001103/100000000000000 : ℝ)^807
        have hw : |(4338448071/10000000000 : ℝ)|=(4338448071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064680623/5000000000 : ℝ)|^1063 ≤ (623823301519/2000000000000 : ℝ)^807
        have hw : |(2064680623/5000000000 : ℝ)|=(2064680623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139407529/2500000000 : ℝ)|^1063 ≤ (35520806902627/100000000000000 : ℝ)^807
        have hw : |(1139407529/2500000000 : ℝ)|=(1139407529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-130352321/625000000 : ℝ)*x 0 + (522659103/1000000000 : ℝ)*x 1 + (84893281/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130352321/625000000 : ℝ)^1063 ≤ (2536966570811/20000000000000 : ℝ)^807 := by
    have hnat : (130352321 : ℕ)^1063*20000000000000^807 ≤ 2536966570811^807*625000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130352321 625000000 2536966570811 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522659103/1000000000 : ℝ)^1063 ≤ (33236908349/78125000000 : ℝ)^807 := by
    have hnat : (522659103 : ℕ)^1063*78125000000^807 ≤ 33236908349^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522659103 1000000000 33236908349 78125000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84893281/156250000 : ℝ)^1063 ≤ (11192981113877/25000000000000 : ℝ)^807 := by
    have hnat : (84893281 : ℕ)^1063*25000000000000^807 ≤ 11192981113877^807*156250000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84893281 156250000 11192981113877 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130352321/625000000 : ℝ), (522659103/1000000000 : ℝ), (84893281/156250000 : ℝ)] ![(2536966570811/20000000000000 : ℝ), (33236908349/78125000000 : ℝ), (11192981113877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130352321/625000000 : ℝ)|^1063 ≤ (2536966570811/20000000000000 : ℝ)^807
        have hw : |(-130352321/625000000 : ℝ)|=(130352321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522659103/1000000000 : ℝ)|^1063 ≤ (33236908349/78125000000 : ℝ)^807
        have hw : |(522659103/1000000000 : ℝ)|=(522659103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84893281/156250000 : ℝ)|^1063 ≤ (11192981113877/25000000000000 : ℝ)^807
        have hw : |(84893281/156250000 : ℝ)|=(84893281/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265059763/500000000 : ℝ)*x 0 + (-992391959/5000000000 : ℝ)*x 1 + (5433169937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265059763/500000000 : ℝ)^1063 ≤ (21672473506303/50000000000000 : ℝ)^807 := by
    have hnat : (265059763 : ℕ)^1063*50000000000000^807 ≤ 21672473506303^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265059763 500000000 21672473506303 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992391959/5000000000 : ℝ)^1063 ≤ (5941564515503/50000000000000 : ℝ)^807 := by
    have hnat : (992391959 : ℕ)^1063*50000000000000^807 ≤ 5941564515503^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992391959 5000000000 5941564515503 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433169937/10000000000 : ℝ)^1063 ≤ (349780655823/781250000000 : ℝ)^807 := by
    have hnat : (5433169937 : ℕ)^1063*781250000000^807 ≤ 349780655823^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433169937 10000000000 349780655823 781250000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265059763/500000000 : ℝ), (-992391959/5000000000 : ℝ), (5433169937/10000000000 : ℝ)] ![(21672473506303/50000000000000 : ℝ), (5941564515503/50000000000000 : ℝ), (349780655823/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265059763/500000000 : ℝ)|^1063 ≤ (21672473506303/50000000000000 : ℝ)^807
        have hw : |(265059763/500000000 : ℝ)|=(265059763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992391959/5000000000 : ℝ)|^1063 ≤ (5941564515503/50000000000000 : ℝ)^807
        have hw : |(-992391959/5000000000 : ℝ)|=(992391959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433169937/10000000000 : ℝ)|^1063 ≤ (349780655823/781250000000 : ℝ)^807
        have hw : |(5433169937/10000000000 : ℝ)|=(5433169937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5301195297/10000000000 : ℝ)*x 0 + (5433169877/10000000000 : ℝ)*x 1 + (-1984783949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301195297/10000000000 : ℝ)^1063 ≤ (1354529606597/3125000000000 : ℝ)^807 := by
    have hnat : (5301195297 : ℕ)^1063*3125000000000^807 ≤ 1354529606597^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301195297 10000000000 1354529606597 3125000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433169877/10000000000 : ℝ)^1063 ≤ (4477192329407/10000000000000 : ℝ)^807 := by
    have hnat : (5433169877 : ℕ)^1063*10000000000000^807 ≤ 4477192329407^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433169877 10000000000 4477192329407 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984783949/10000000000 : ℝ)^1063 ≤ (2970782318871/25000000000000 : ℝ)^807 := by
    have hnat : (1984783949 : ℕ)^1063*25000000000000^807 ≤ 2970782318871^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984783949 10000000000 2970782318871 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301195297/10000000000 : ℝ), (5433169877/10000000000 : ℝ), (-1984783949/10000000000 : ℝ)] ![(1354529606597/3125000000000 : ℝ), (4477192329407/10000000000000 : ℝ), (2970782318871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301195297/10000000000 : ℝ)|^1063 ≤ (1354529606597/3125000000000 : ℝ)^807
        have hw : |(5301195297/10000000000 : ℝ)|=(5301195297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433169877/10000000000 : ℝ)|^1063 ≤ (4477192329407/10000000000000 : ℝ)^807
        have hw : |(5433169877/10000000000 : ℝ)|=(5433169877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984783949/10000000000 : ℝ)|^1063 ≤ (2970782318871/25000000000000 : ℝ)^807
        have hw : |(-1984783949/10000000000 : ℝ)|=(1984783949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s3_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4338494197/10000000000 : ℝ)*x 0 + (4555785779/10000000000 : ℝ)*x 1 + (2065608561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338494197/10000000000 : ℝ)^1063 ≤ (4161061773481/12500000000000 : ℝ)^807 := by
    have hnat : (4338494197 : ℕ)^1063*12500000000000^807 ≤ 4161061773481^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338494197 10000000000 4161061773481 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555785779/10000000000 : ℝ)^1063 ≤ (35501874057759/100000000000000 : ℝ)^807 := by
    have hnat : (4555785779 : ℕ)^1063*100000000000000^807 ≤ 35501874057759^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555785779 10000000000 35501874057759 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065608561/5000000000 : ℝ)^1063 ≤ (15604815868111/50000000000000 : ℝ)^807 := by
    have hnat : (2065608561 : ℕ)^1063*50000000000000^807 ≤ 15604815868111^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065608561 5000000000 15604815868111 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338494197/10000000000 : ℝ), (4555785779/10000000000 : ℝ), (2065608561/5000000000 : ℝ)] ![(4161061773481/12500000000000 : ℝ), (35501874057759/100000000000000 : ℝ), (15604815868111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338494197/10000000000 : ℝ)|^1063 ≤ (4161061773481/12500000000000 : ℝ)^807
        have hw : |(4338494197/10000000000 : ℝ)|=(4338494197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555785779/10000000000 : ℝ)|^1063 ≤ (35501874057759/100000000000000 : ℝ)^807
        have hw : |(4555785779/10000000000 : ℝ)|=(4555785779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065608561/5000000000 : ℝ)|^1063 ≤ (15604815868111/50000000000000 : ℝ)^807
        have hw : |(2065608561/5000000000 : ℝ)|=(2065608561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5329/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7533/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1901/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1901/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1901/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1901/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1901/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1901/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1901/20000 : ℝ) ^ (4251/1024 : ℝ) ≤ (5716154674080271/100000000000000000000 : ℝ) := by
    have hpowers : (1901/20000 : ℝ)^4251 ≤ (5716154674080271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1901 : ℕ)^4251*100000000000000000000^1024 ≤ 5716154674080271^1024*20000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1901 20000 5716154674080271 100000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1901/20000 : ℝ)) (X := (5716154674080271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16317/100000 : ℝ) ^ (4251/1024 : ℝ) ≤ (10774839966449309/20000000000000000000 : ℝ) := by
    have hpowers : (16317/100000 : ℝ)^4251 ≤ (10774839966449309/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16317 : ℕ)^4251*20000000000000000000^1024 ≤ 10774839966449309^1024*100000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16317 100000 10774839966449309 20000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16317/100000 : ℝ)) (X := (10774839966449309/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005716154674080271/50000000000000000000 : ℝ) ≤ (10000275374660729/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50005716154674080271/50000000000000000000 : ℝ)^1024 ≤ (10000275374660729/10000000000000000 : ℝ)^4251 := by
      have hnat : (50005716154674080271 : ℕ)^1024*10000000000000000^4251 ≤ 10000275374660729^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005716154674080271 50000000000000000000 10000275374660729 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000275374660729/10000000000000000 : ℝ)) (X := (50005716154674080271/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126862198578322713/3125000000000000000 : ℝ) ≤ (39068105916827/39062500000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (3126862198578322713/3125000000000000000 : ℝ)^1024 ≤ (39068105916827/39062500000000 : ℝ)^4251 := by
      have hnat : (3126862198578322713 : ℕ)^1024*39062500000000^4251 ≤ 39068105916827^4251*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126862198578322713 3125000000000000000 39068105916827 39062500000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39068105916827/39062500000000 : ℝ)) (X := (3126862198578322713/3125000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10010774839966449309/10000000000000000000 : ℝ) ≤ (2000518970950939/2000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (10010774839966449309/10000000000000000000 : ℝ)^1024 ≤ (2000518970950939/2000000000000000 : ℝ)^4251 := by
      have hnat : (10010774839966449309 : ℕ)^1024*2000000000000000^4251 ≤ 2000518970950939^4251*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010774839966449309 10000000000000000000 2000518970950939 2000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000518970950939/2000000000000000 : ℝ)) (X := (10010774839966449309/10000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5716154674080271/100000000000000000000 : ℝ) ≤ ((34049914596947869559/34060000000000000000 : ℝ)+2*(1159740046983/681200000000000 : ℝ)*(1901/20000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (34049914596947869559/34060000000000000000 : ℝ)+2*(1159740046983/681200000000000 : ℝ)*(1901/20000 : ℝ)=(10000275374660729/10000000000000000 : ℝ) by norm_num, show 1+2*(5716154674080271/100000000000000000000 : ℝ)=(50005716154674080271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10774839966449309/20000000000000000000 : ℝ)+(5716154674080271/100000000000000000000 : ℝ) ≤ ((34049914596947869559/34060000000000000000 : ℝ)+(1159740046983/681200000000000 : ℝ)*((16317/100000 : ℝ)+(1901/20000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (34049914596947869559/34060000000000000000 : ℝ)+(1159740046983/681200000000000 : ℝ)*((16317/100000 : ℝ)+(1901/20000 : ℝ))=(39068105916827/39062500000000 : ℝ) by norm_num, show 1+(10774839966449309/20000000000000000000 : ℝ)+(5716154674080271/100000000000000000000 : ℝ)=(3126862198578322713/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10774839966449309/20000000000000000000 : ℝ) ≤ ((34049914596947869559/34060000000000000000 : ℝ)+2*(1159740046983/681200000000000 : ℝ)*(16317/100000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (34049914596947869559/34060000000000000000 : ℝ)+2*(1159740046983/681200000000000 : ℝ)*(16317/100000 : ℝ)=(2000518970950939/2000000000000000 : ℝ) by norm_num, show 1+2*(10774839966449309/20000000000000000000 : ℝ)=(10010774839966449309/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34049914596947869559/34060000000000000000 : ℝ)*(X 1 0+X 2 0)+(1159740046983/681200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (1901/20000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (34049914596947869559/34060000000000000000 : ℝ)) (alpha := (1159740046983/681200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34049914596947869559/34060000000000000000 : ℝ)*(X 0 1+X 2 1)+(1159740046983/681200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (1901/20000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (34049914596947869559/34060000000000000000 : ℝ)) (alpha := (1159740046983/681200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34049914596947869559/34060000000000000000 : ℝ)*(X 0 2+X 1 2)+(1159740046983/681200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (1901/20000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (34049914596947869559/34060000000000000000 : ℝ)) (alpha := (1159740046983/681200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-417122913/2000000000 : ℝ)*X 0 0+(5434072899/10000000000 : ℝ)*X 0 1+(5225693759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354549759/10000000000 : ℝ)*X 1 0+(-10961301/50000000 : ℝ)*X 1 1+(209027753/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677274901/5000000000 : ℝ)*X 2 0+(5225693589/10000000000 : ℝ)*X 2 1+(-2192260453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338448071/10000000000 : ℝ)*X 0 0+(2064680623/5000000000 : ℝ)*X 0 1+(1139407529/2500000000 : ℝ)*X 0 2+(4338448071/10000000000 : ℝ)*X 1 0+(2064680623/5000000000 : ℝ)*X 1 1+(1139407529/2500000000 : ℝ)*X 1 2+(4338448071/10000000000 : ℝ)*X 2 0+(2064680623/5000000000 : ℝ)*X 2 1+(1139407529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-130352321/625000000 : ℝ)*X 0 0+(522659103/1000000000 : ℝ)*X 0 1+(84893281/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265059763/500000000 : ℝ)*X 1 0+(-992391959/5000000000 : ℝ)*X 1 1+(5433169937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301195297/10000000000 : ℝ)*X 2 0+(5433169877/10000000000 : ℝ)*X 2 1+(-1984783949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338494197/10000000000 : ℝ)*X 0 0+(4555785779/10000000000 : ℝ)*X 0 1+(2065608561/5000000000 : ℝ)*X 0 2+(4338494197/10000000000 : ℝ)*X 1 0+(4555785779/10000000000 : ℝ)*X 1 1+(2065608561/5000000000 : ℝ)*X 1 2+(4338494197/10000000000 : ℝ)*X 2 0+(4555785779/10000000000 : ℝ)*X 2 1+(2065608561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2424396529170924467485807773/425750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224347651/20000000000000 : ℝ)*(base19) + (27877343/2500000000000 : ℝ)*(base23) + (54471403/100000000000000 : ℝ)*(lower2) + (283210979/100000000000000 : ℝ)*(upper3) + (3784743/12500000000000 : ℝ)*(lower4) + (891747627761283/25000000000000 : ℝ)*(major0) + (891747627761283/25000000000000 : ℝ)*(major1) + (891747627761283/25000000000000 : ℝ)*(major2) + (4798966420965769/100000000000000 : ℝ)*(sp0) + (959795797648137/20000000000000 : ℝ)*(sp1) + (4798978994885219/100000000000000 : ℝ)*(sp2) + (583747330034629/25000000000000 : ℝ)*(sp3) + (13689013171/100000000000000 : ℝ)*(sp4) + (11402159013/100000000000000 : ℝ)*(sp7) + (291875090287191/12500000000000 : ℝ)*(f.failure) + (239949005498947/5000000000000 : ℝ)*(f.sum) + (42538155386349/8515000000000000000000000000 : ℝ)*base65 + (487360380173235831/65500000000000000000000000000000 : ℝ)*base68 + (1164596703544735831/65500000000000000000000000000000 : ℝ)*base70 + (1173395432187235831/65500000000000000000000000000000 : ℝ)*base72 + (3872929996593/1064375000000000000000000000 : ℝ)*base73 + (1043059828489735831/65500000000000000000000000000000 : ℝ)*base76 + (826797710043735831/65500000000000000000000000000000 : ℝ)*base78 + (21597119888235831/65500000000000000000000000000000 : ℝ)*base80 + (9921134750459/2128750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8951931/1250000000000000000000 : ℝ)*base90 + (8951931/1250000000000000000000 : ℝ)*base92 + (8951931/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2237965093805680484114514663/425750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357465679/25000000000000 : ℝ)*(base19) + (1498015213/100000000000000 : ℝ)*(base23) + (136383827/100000000000000 : ℝ)*(upper3) + (20188537/100000000000000 : ℝ)*(lower4) + (38279737/25000000000000 : ℝ)*(upper5) + (1799024025447581/50000000000000 : ℝ)*(major0) + (1799024025447581/50000000000000 : ℝ)*(major1) + (1799024025447581/50000000000000 : ℝ)*(major2) + (4760630783/20000000000000 : ℝ)*(sp1) + (4686769973/20000000000000 : ℝ)*(sp2) + (4840764514367943/100000000000000 : ℝ)*(sp4) + (302546205084457/6250000000000 : ℝ)*(sp5) + (302546223906429/6250000000000 : ℝ)*(sp6) + (1177665706102451/50000000000000 : ℝ)*(sp7) + (1177665706102451/50000000000000 : ℝ)*(f.failure) + (4840764514367943/100000000000000 : ℝ)*(f.sum) + (82807365442743/17030000000000000000000000000 : ℝ)*base65 + (239596425603248983/131000000000000000000000000000000 : ℝ)*base67 + (702299559555248983/131000000000000000000000000000000 : ℝ)*base69 + (1966025598622248983/131000000000000000000000000000000 : ℝ)*base71 + (105510081573137/17030000000000000000000000000 : ℝ)*base74 + (292587709661751017/131000000000000000000000000000000 : ℝ)*base76 + (618432563599248983/131000000000000000000000000000000 : ℝ)*base77 + (3505859783690248983/131000000000000000000000000000000 : ℝ)*base79 + (84238045170767/17030000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (40783591/5000000000000000000000 : ℝ)*base90 + (40783591/5000000000000000000000 : ℝ)*base92 + (40783591/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1292_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7533/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1292_s4_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1043767519/5000000000 : ℝ)*x 0 + (541892953/1000000000 : ℝ)*x 1 + (1047915651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043767519/5000000000 : ℝ)^1063 ≤ (6350019903069/50000000000000 : ℝ)^807 := by
    have hnat : (1043767519 : ℕ)^1063*50000000000000^807 ≤ 6350019903069^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043767519 5000000000 6350019903069 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541892953/1000000000 : ℝ)^1063 ≤ (22308707450239/50000000000000 : ℝ)^807 := by
    have hnat : (541892953 : ℕ)^1063*50000000000000^807 ≤ 22308707450239^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541892953 1000000000 22308707450239 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047915651/2000000000 : ℝ)^1063 ≤ (4268254527983/10000000000000 : ℝ)^807 := by
    have hnat : (1047915651 : ℕ)^1063*10000000000000^807 ≤ 4268254527983^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047915651 2000000000 4268254527983 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1043767519/5000000000 : ℝ), (541892953/1000000000 : ℝ), (1047915651/2000000000 : ℝ)] ![(6350019903069/50000000000000 : ℝ), (22308707450239/50000000000000 : ℝ), (4268254527983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1043767519/5000000000 : ℝ)|^1063 ≤ (6350019903069/50000000000000 : ℝ)^807
        have hw : |(-1043767519/5000000000 : ℝ)|=(1043767519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541892953/1000000000 : ℝ)|^1063 ≤ (22308707450239/50000000000000 : ℝ)^807
        have hw : |(541892953/1000000000 : ℝ)|=(541892953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047915651/2000000000 : ℝ)|^1063 ≤ (4268254527983/10000000000000 : ℝ)^807
        have hw : |(1047915651/2000000000 : ℝ)|=(1047915651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267536107/500000000 : ℝ)*x 0 + (-136189449/625000000 : ℝ)*x 1 + (5239578009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267536107/500000000 : ℝ)^1063 ≤ (1371223467627/3125000000000 : ℝ)^807 := by
    have hnat : (267536107 : ℕ)^1063*3125000000000^807 ≤ 1371223467627^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267536107 500000000 1371223467627 3125000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136189449/625000000 : ℝ)^1063 ≤ (13438306382793/100000000000000 : ℝ)^807 := by
    have hnat : (136189449 : ℕ)^1063*100000000000000^807 ≤ 13438306382793^807*625000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136189449 625000000 13438306382793 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239578009/10000000000 : ℝ)^1063 ≤ (8536508528033/20000000000000 : ℝ)^807 := by
    have hnat : (5239578009 : ℕ)^1063*20000000000000^807 ≤ 8536508528033^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239578009 10000000000 8536508528033 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267536107/500000000 : ℝ), (-136189449/625000000 : ℝ), (5239578009/10000000000 : ℝ)] ![(1371223467627/3125000000000 : ℝ), (13438306382793/100000000000000 : ℝ), (8536508528033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267536107/500000000 : ℝ)|^1063 ≤ (1371223467627/3125000000000 : ℝ)^807
        have hw : |(267536107/500000000 : ℝ)|=(267536107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136189449/625000000 : ℝ)|^1063 ≤ (13438306382793/100000000000000 : ℝ)^807
        have hw : |(-136189449/625000000 : ℝ)|=(136189449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239578009/10000000000 : ℝ)|^1063 ≤ (8536508528033/20000000000000 : ℝ)^807
        have hw : |(5239578009/10000000000 : ℝ)|=(5239578009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675360937/5000000000 : ℝ)*x 0 + (5239578633/10000000000 : ℝ)*x 1 + (-2179030713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675360937/5000000000 : ℝ)^1063 ≤ (43879148090723/100000000000000 : ℝ)^807 := by
    have hnat : (2675360937 : ℕ)^1063*100000000000000^807 ≤ 43879148090723^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675360937 5000000000 43879148090723 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239578633/10000000000 : ℝ)^1063 ≤ (42682549335901/100000000000000 : ℝ)^807 := by
    have hnat : (5239578633 : ℕ)^1063*100000000000000^807 ≤ 42682549335901^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239578633 10000000000 42682549335901 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179030713/10000000000 : ℝ)^1063 ≤ (2687660511329/20000000000000 : ℝ)^807 := by
    have hnat : (2179030713 : ℕ)^1063*20000000000000^807 ≤ 2687660511329^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179030713 10000000000 2687660511329 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675360937/5000000000 : ℝ), (5239578633/10000000000 : ℝ), (-2179030713/10000000000 : ℝ)] ![(43879148090723/100000000000000 : ℝ), (42682549335901/100000000000000 : ℝ), (2687660511329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675360937/5000000000 : ℝ)|^1063 ≤ (43879148090723/100000000000000 : ℝ)^807
        have hw : |(2675360937/5000000000 : ℝ)|=(2675360937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239578633/10000000000 : ℝ)|^1063 ≤ (42682549335901/100000000000000 : ℝ)^807
        have hw : |(5239578633/10000000000 : ℝ)|=(5239578633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179030713/10000000000 : ℝ)|^1063 ≤ (2687660511329/20000000000000 : ℝ)^807
        have hw : |(-2179030713/10000000000 : ℝ)|=(2179030713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2169804389/5000000000 : ℝ)*x 0 + (2079522537/5000000000 : ℝ)*x 1 + (2263827147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169804389/5000000000 : ℝ)^1063 ≤ (1040617485153/3125000000000 : ℝ)^807 := by
    have hnat : (2169804389 : ℕ)^1063*3125000000000^807 ≤ 1040617485153^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169804389 5000000000 1040617485153 3125000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079522537/5000000000 : ℝ)^1063 ≤ (7871711352617/25000000000000 : ℝ)^807 := by
    have hnat : (2079522537 : ℕ)^1063*25000000000000^807 ≤ 7871711352617^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079522537 5000000000 7871711352617 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263827147/5000000000 : ℝ)^1063 ≤ (35213395053391/100000000000000 : ℝ)^807 := by
    have hnat : (2263827147 : ℕ)^1063*100000000000000^807 ≤ 35213395053391^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263827147 5000000000 35213395053391 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169804389/5000000000 : ℝ), (2079522537/5000000000 : ℝ), (2263827147/5000000000 : ℝ)] ![(1040617485153/3125000000000 : ℝ), (7871711352617/25000000000000 : ℝ), (35213395053391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169804389/5000000000 : ℝ)|^1063 ≤ (1040617485153/3125000000000 : ℝ)^807
        have hw : |(2169804389/5000000000 : ℝ)|=(2169804389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079522537/5000000000 : ℝ)|^1063 ≤ (7871711352617/25000000000000 : ℝ)^807
        have hw : |(2079522537/5000000000 : ℝ)|=(2079522537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263827147/5000000000 : ℝ)|^1063 ≤ (35213395053391/100000000000000 : ℝ)^807
        have hw : |(2263827147/5000000000 : ℝ)|=(2263827147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1043774851/5000000000 : ℝ)*x 0 + (2620121793/5000000000 : ℝ)*x 1 + (5418260403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043774851/5000000000 : ℝ)^1063 ≤ (6350078659307/50000000000000 : ℝ)^807 := by
    have hnat : (1043774851 : ℕ)^1063*50000000000000^807 ≤ 6350078659307^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043774851 5000000000 6350078659307 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620121793/5000000000 : ℝ)^1063 ≤ (21344842327581/50000000000000 : ℝ)^807 := by
    have hnat : (2620121793 : ℕ)^1063*50000000000000^807 ≤ 21344842327581^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620121793 5000000000 21344842327581 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418260403/10000000000 : ℝ)^1063 ≤ (278813487551/625000000000 : ℝ)^807 := by
    have hnat : (5418260403 : ℕ)^1063*625000000000^807 ≤ 278813487551^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418260403 10000000000 278813487551 625000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1043774851/5000000000 : ℝ), (2620121793/5000000000 : ℝ), (5418260403/10000000000 : ℝ)] ![(6350078659307/50000000000000 : ℝ), (21344842327581/50000000000000 : ℝ), (278813487551/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1043774851/5000000000 : ℝ)|^1063 ≤ (6350078659307/50000000000000 : ℝ)^807
        have hw : |(-1043774851/5000000000 : ℝ)|=(1043774851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620121793/5000000000 : ℝ)|^1063 ≤ (21344842327581/50000000000000 : ℝ)^807
        have hw : |(2620121793/5000000000 : ℝ)|=(2620121793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418260403/10000000000 : ℝ)|^1063 ≤ (278813487551/625000000000 : ℝ)^807
        have hw : |(5418260403/10000000000 : ℝ)|=(5418260403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304803323/10000000000 : ℝ)*x 0 + (-2000348721/10000000000 : ℝ)*x 1 + (677282549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304803323/10000000000 : ℝ)^1063 ≤ (10845952706029/25000000000000 : ℝ)^807 := by
    have hnat : (5304803323 : ℕ)^1063*25000000000000^807 ≤ 10845952706029^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304803323 10000000000 10845952706029 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000348721/10000000000 : ℝ)^1063 ≤ (480241251299/4000000000000 : ℝ)^807 := by
    have hnat : (2000348721 : ℕ)^1063*4000000000000^807 ≤ 480241251299^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000348721 10000000000 480241251299 4000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677282549/1250000000 : ℝ)^1063 ≤ (1394067434027/3125000000000 : ℝ)^807 := by
    have hnat : (677282549 : ℕ)^1063*3125000000000^807 ≤ 1394067434027^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677282549 1250000000 1394067434027 3125000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304803323/10000000000 : ℝ), (-2000348721/10000000000 : ℝ), (677282549/1250000000 : ℝ)] ![(10845952706029/25000000000000 : ℝ), (480241251299/4000000000000 : ℝ), (1394067434027/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304803323/10000000000 : ℝ)|^1063 ≤ (10845952706029/25000000000000 : ℝ)^807
        have hw : |(5304803323/10000000000 : ℝ)|=(5304803323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000348721/10000000000 : ℝ)|^1063 ≤ (480241251299/4000000000000 : ℝ)^807
        have hw : |(-2000348721/10000000000 : ℝ)|=(2000348721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677282549/1250000000 : ℝ)|^1063 ≤ (1394067434027/3125000000000 : ℝ)^807
        have hw : |(677282549/1250000000 : ℝ)|=(677282549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530480329/1000000000 : ℝ)*x 0 + (5418260427/10000000000 : ℝ)*x 1 + (-500087179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530480329/1000000000 : ℝ)^1063 ≤ (21691905234311/50000000000000 : ℝ)^807 := by
    have hnat : (530480329 : ℕ)^1063*50000000000000^807 ≤ 21691905234311^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530480329 1000000000 21691905234311 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418260427/10000000000 : ℝ)^1063 ≤ (22305079134221/50000000000000 : ℝ)^807 := by
    have hnat : (5418260427 : ℕ)^1063*50000000000000^807 ≤ 22305079134221^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418260427 10000000000 22305079134221 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500087179/2500000000 : ℝ)^1063 ≤ (6003015621473/50000000000000 : ℝ)^807 := by
    have hnat : (500087179 : ℕ)^1063*50000000000000^807 ≤ 6003015621473^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500087179 2500000000 6003015621473 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530480329/1000000000 : ℝ), (5418260427/10000000000 : ℝ), (-500087179/2500000000 : ℝ)] ![(21691905234311/50000000000000 : ℝ), (22305079134221/50000000000000 : ℝ), (6003015621473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530480329/1000000000 : ℝ)|^1063 ≤ (21691905234311/50000000000000 : ℝ)^807
        have hw : |(530480329/1000000000 : ℝ)|=(530480329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418260427/10000000000 : ℝ)|^1063 ≤ (22305079134221/50000000000000 : ℝ)^807
        have hw : |(5418260427/10000000000 : ℝ)|=(5418260427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500087179/2500000000 : ℝ)|^1063 ≤ (6003015621473/50000000000000 : ℝ)^807
        have hw : |(-500087179/2500000000 : ℝ)|=(500087179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s4_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (867927693/2000000000 : ℝ)*x 0 + (226314331/500000000 : ℝ)*x 1 + (2080209931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867927693/2000000000 : ℝ)^1063 ≤ (4162507448883/12500000000000 : ℝ)^807 := by
    have hnat : (867927693 : ℕ)^1063*12500000000000^807 ≤ 4162507448883^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867927693 2000000000 4162507448883 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226314331/500000000 : ℝ)^1063 ≤ (35199384472219/100000000000000 : ℝ)^807 := by
    have hnat : (226314331 : ℕ)^1063*100000000000000^807 ≤ 35199384472219^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226314331 500000000 35199384472219 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080209931/5000000000 : ℝ)^1063 ≤ (630011118501/2000000000000 : ℝ)^807 := by
    have hnat : (2080209931 : ℕ)^1063*2000000000000^807 ≤ 630011118501^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080209931 5000000000 630011118501 2000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867927693/2000000000 : ℝ), (226314331/500000000 : ℝ), (2080209931/5000000000 : ℝ)] ![(4162507448883/12500000000000 : ℝ), (35199384472219/100000000000000 : ℝ), (630011118501/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867927693/2000000000 : ℝ)|^1063 ≤ (4162507448883/12500000000000 : ℝ)^807
        have hw : |(867927693/2000000000 : ℝ)|=(867927693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226314331/500000000 : ℝ)|^1063 ≤ (35199384472219/100000000000000 : ℝ)^807
        have hw : |(226314331/500000000 : ℝ)|=(226314331/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080209931/5000000000 : ℝ)|^1063 ≤ (630011118501/2000000000000 : ℝ)^807
        have hw : |(2080209931/5000000000 : ℝ)|=(2080209931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2191/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7533/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7533/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7533/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7533/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7533/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7533/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5329/50000 : ℝ) ^ (4251/1024 : ℝ) ≤ (2298607821087063/25000000000000000000 : ℝ) := by
    have hpowers : (5329/50000 : ℝ)^4251 ≤ (2298607821087063/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5329 : ℕ)^4251*25000000000000000000^1024 ≤ 2298607821087063^1024*50000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5329 50000 2298607821087063 25000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5329/50000 : ℝ)) (X := (2298607821087063/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7533/50000 : ℝ) ^ (4251/1024 : ℝ) ≤ (19343618586733883/50000000000000000000 : ℝ) := by
    have hpowers : (7533/50000 : ℝ)^4251 ≤ (19343618586733883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7533 : ℕ)^4251*50000000000000000000^1024 ≤ 19343618586733883^1024*50000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7533 50000 19343618586733883 50000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7533/50000 : ℝ)) (X := (19343618586733883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502298607821087063/12500000000000000000 : ℝ) ≤ (10000442928278831/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (12502298607821087063/12500000000000000000 : ℝ)^1024 ≤ (10000442928278831/10000000000000000 : ℝ)^4251 := by
      have hnat : (12502298607821087063 : ℕ)^1024*10000000000000000^4251 ≤ 10000442928278831^4251*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502298607821087063 12500000000000000000 10000442928278831 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000442928278831/10000000000000000 : ℝ)) (X := (12502298607821087063/12500000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023940834228908009/50000000000000000000 : ℝ) ≤ (2500288296402073/2500000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50023940834228908009/50000000000000000000 : ℝ)^1024 ≤ (2500288296402073/2500000000000000 : ℝ)^4251 := by
      have hnat : (50023940834228908009 : ℕ)^1024*2500000000000000^4251 ≤ 2500288296402073^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023940834228908009 50000000000000000000 2500288296402073 2500000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500288296402073/2500000000000000 : ℝ)) (X := (50023940834228908009/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019343618586733883/25000000000000000000 : ℝ) ≤ (10001863442937753/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (25019343618586733883/25000000000000000000 : ℝ)^1024 ≤ (10001863442937753/10000000000000000 : ℝ)^4251 := by
      have hnat : (25019343618586733883 : ℕ)^1024*10000000000000000^4251 ≤ 10001863442937753^4251*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019343618586733883 25000000000000000000 10001863442937753 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001863442937753/10000000000000000 : ℝ)) (X := (25019343618586733883/25000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2298607821087063/25000000000000000000 : ℝ) ≤ ((11016703145654574093/11020000000000000000 : ℝ)+2*(710257329461/440800000000000 : ℝ)*(5329/50000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (11016703145654574093/11020000000000000000 : ℝ)+2*(710257329461/440800000000000 : ℝ)*(5329/50000 : ℝ)=(10000442928278831/10000000000000000 : ℝ) by norm_num, show 1+2*(2298607821087063/25000000000000000000 : ℝ)=(12502298607821087063/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19343618586733883/50000000000000000000 : ℝ)+(2298607821087063/25000000000000000000 : ℝ) ≤ ((11016703145654574093/11020000000000000000 : ℝ)+(710257329461/440800000000000 : ℝ)*((7533/50000 : ℝ)+(5329/50000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (11016703145654574093/11020000000000000000 : ℝ)+(710257329461/440800000000000 : ℝ)*((7533/50000 : ℝ)+(5329/50000 : ℝ))=(2500288296402073/2500000000000000 : ℝ) by norm_num, show 1+(19343618586733883/50000000000000000000 : ℝ)+(2298607821087063/25000000000000000000 : ℝ)=(50023940834228908009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19343618586733883/50000000000000000000 : ℝ) ≤ ((11016703145654574093/11020000000000000000 : ℝ)+2*(710257329461/440800000000000 : ℝ)*(7533/50000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (11016703145654574093/11020000000000000000 : ℝ)+2*(710257329461/440800000000000 : ℝ)*(7533/50000 : ℝ)=(10001863442937753/10000000000000000 : ℝ) by norm_num, show 1+2*(19343618586733883/50000000000000000000 : ℝ)=(25019343618586733883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11016703145654574093/11020000000000000000 : ℝ)*(X 1 0+X 2 0)+(710257329461/440800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (7533/50000 : ℝ)) (c := (11016703145654574093/11020000000000000000 : ℝ)) (alpha := (710257329461/440800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11016703145654574093/11020000000000000000 : ℝ)*(X 0 1+X 2 1)+(710257329461/440800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (7533/50000 : ℝ)) (c := (11016703145654574093/11020000000000000000 : ℝ)) (alpha := (710257329461/440800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11016703145654574093/11020000000000000000 : ℝ)*(X 0 2+X 1 2)+(710257329461/440800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (7533/50000 : ℝ)) (c := (11016703145654574093/11020000000000000000 : ℝ)) (alpha := (710257329461/440800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1043767519/5000000000 : ℝ)*X 0 0+(541892953/1000000000 : ℝ)*X 0 1+(1047915651/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267536107/500000000 : ℝ)*X 1 0+(-136189449/625000000 : ℝ)*X 1 1+(5239578009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675360937/5000000000 : ℝ)*X 2 0+(5239578633/10000000000 : ℝ)*X 2 1+(-2179030713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169804389/5000000000 : ℝ)*X 0 0+(2079522537/5000000000 : ℝ)*X 0 1+(2263827147/5000000000 : ℝ)*X 0 2+(2169804389/5000000000 : ℝ)*X 1 0+(2079522537/5000000000 : ℝ)*X 1 1+(2263827147/5000000000 : ℝ)*X 1 2+(2169804389/5000000000 : ℝ)*X 2 0+(2079522537/5000000000 : ℝ)*X 2 1+(2263827147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1043774851/5000000000 : ℝ)*X 0 0+(2620121793/5000000000 : ℝ)*X 0 1+(5418260403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304803323/10000000000 : ℝ)*X 1 0+(-2000348721/10000000000 : ℝ)*X 1 1+(677282549/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530480329/1000000000 : ℝ)*X 2 0+(5418260427/10000000000 : ℝ)*X 2 1+(-500087179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867927693/2000000000 : ℝ)*X 0 0+(226314331/500000000 : ℝ)*X 0 1+(2080209931/5000000000 : ℝ)*X 0 2+(867927693/2000000000 : ℝ)*X 1 0+(226314331/500000000 : ℝ)*X 1 1+(2080209931/5000000000 : ℝ)*X 1 2+(867927693/2000000000 : ℝ)*X 2 0+(226314331/500000000 : ℝ)*X 2 1+(2080209931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (435096472221377628773551677/137750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117595953/100000000000000 : ℝ)*(base21) + (47021931/100000000000000 : ℝ)*(lower2) + (79577109/100000000000000 : ℝ)*(lower3) + (76373461/100000000000000 : ℝ)*(lower4) + (1036072196756037/25000000000000 : ℝ)*(major0) + (1036072196756037/25000000000000 : ℝ)*(major1) + (1036072196756037/25000000000000 : ℝ)*(major2) + (1393914657533301/25000000000000 : ℝ)*(sp0) + (2787827703712879/50000000000000 : ℝ)*(sp1) + (5575669290113661/100000000000000 : ℝ)*(sp2) + (67822616114207/2500000000000 : ℝ)*(sp3) + (10777576411/100000000000000 : ℝ)*(sp4) + (875017741/6250000000000 : ℝ)*(sp5) + (213530243/6250000000000 : ℝ)*(sp7) + (339113507631521/12500000000000 : ℝ)*(f.failure) + (2787834703854807/50000000000000 : ℝ)*(f.sum) + (16904963291803/5510000000000000000000000000 : ℝ)*base66 + (322889182160025559/275500000000000000000000000000000 : ℝ)*base68 + (66898765076525559/275500000000000000000000000000000 : ℝ)*base70 + (2532543207228974441/275500000000000000000000000000000 : ℝ)*base71 + (3185526273737/5510000000000000000000000000 : ℝ)*base73 + (2914354309287974441/275500000000000000000000000000000 : ℝ)*base75 + (2017362310525974441/275500000000000000000000000000000 : ℝ)*base77 + (2718564299191474441/275500000000000000000000000000000 : ℝ)*base79 + (6936393474727/5510000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (15042461/1250000000000000000000 : ℝ)*base90 + (15042461/1250000000000000000000 : ℝ)*base92 + (15042461/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237015545293951588644730791/34437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135006133/10000000000000 : ℝ)*(base19) + (686590097/50000000000000 : ℝ)*(base23) + (14979733/10000000000000 : ℝ)*(upper3) + (13402727/50000000000000 : ℝ)*(lower4) + (15418563/10000000000000 : ℝ)*(upper5) + (521917598943171/12500000000000 : ℝ)*(major0) + (521917598943171/12500000000000 : ℝ)*(major1) + (521917598943171/12500000000000 : ℝ)*(major2) + (25888753941/100000000000000 : ℝ)*(sp1) + (26759168583/100000000000000 : ℝ)*(sp2) + (5617446226216917/100000000000000 : ℝ)*(sp4) + (2808709493700823/50000000000000 : ℝ)*(sp5) + (280870904693407/5000000000000 : ℝ)*(sp6) + (1366617563728839/50000000000000 : ℝ)*(sp7) + (1366617563728839/50000000000000 : ℝ)*(f.failure) + (5617446226216917/100000000000000 : ℝ)*(f.sum) + (720433040849/2755000000000000000000000000 : ℝ)*base66 + (449196817018856097/137750000000000000000000000000000 : ℝ)*base68 + (2281417952727393903/137750000000000000000000000000000 : ℝ)*base69 + (1817865829169643903/137750000000000000000000000000000 : ℝ)*base71 + (14712256813919/2755000000000000000000000000 : ℝ)*base74 + (446140106814893903/137750000000000000000000000000000 : ℝ)*base75 + (570891978933643903/137750000000000000000000000000000 : ℝ)*base77 + (336551435529393903/137750000000000000000000000000000 : ℝ)*base79 + (7281191453/86093750000000000000000000 : ℝ)*base81 + (17551701/5000000000000000000000 : ℝ)*base89 + (17551701/5000000000000000000000 : ℝ)*base91 + (17551701/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1292_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2191/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1292_s5_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087892479/10000000000 : ℝ)*x 0 + (5415887881/10000000000 : ℝ)*x 1 + (5242385089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087892479/10000000000 : ℝ)^1063 ≤ (3175726073851/25000000000000 : ℝ)^807 := by
    have hnat : (2087892479 : ℕ)^1063*25000000000000^807 ≤ 3175726073851^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087892479 10000000000 3175726073851 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415887881/10000000000 : ℝ)^1063 ≤ (44584429553649/100000000000000 : ℝ)^807 := by
    have hnat : (5415887881 : ℕ)^1063*100000000000000^807 ≤ 44584429553649^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415887881 10000000000 44584429553649 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242385089/10000000000 : ℝ)^1063 ≤ (5339083267173/12500000000000 : ℝ)^807 := by
    have hnat : (5242385089 : ℕ)^1063*12500000000000^807 ≤ 5339083267173^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242385089 10000000000 5339083267173 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087892479/10000000000 : ℝ), (5415887881/10000000000 : ℝ), (5242385089/10000000000 : ℝ)] ![(3175726073851/25000000000000 : ℝ), (44584429553649/100000000000000 : ℝ), (5339083267173/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087892479/10000000000 : ℝ)|^1063 ≤ (3175726073851/25000000000000 : ℝ)^807
        have hw : |(-2087892479/10000000000 : ℝ)|=(2087892479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415887881/10000000000 : ℝ)|^1063 ≤ (44584429553649/100000000000000 : ℝ)^807
        have hw : |(5415887881/10000000000 : ℝ)|=(5415887881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242385089/10000000000 : ℝ)|^1063 ≤ (5339083267173/12500000000000 : ℝ)^807
        have hw : |(5242385089/10000000000 : ℝ)|=(5242385089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534995143/1000000000 : ℝ)*x 0 + (-1088173631/5000000000 : ℝ)*x 1 + (524238509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534995143/1000000000 : ℝ)^1063 ≤ (43870825918519/100000000000000 : ℝ)^807 := by
    have hnat : (534995143 : ℕ)^1063*100000000000000^807 ≤ 43870825918519^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534995143 1000000000 43870825918519 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088173631/5000000000 : ℝ)^1063 ≤ (13416507921651/100000000000000 : ℝ)^807 := by
    have hnat : (1088173631 : ℕ)^1063*100000000000000^807 ≤ 13416507921651^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088173631 5000000000 13416507921651 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524238509/1000000000 : ℝ)^1063 ≤ (10678166537029/25000000000000 : ℝ)^807 := by
    have hnat : (524238509 : ℕ)^1063*25000000000000^807 ≤ 10678166537029^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524238509 1000000000 10678166537029 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534995143/1000000000 : ℝ), (-1088173631/5000000000 : ℝ), (524238509/1000000000 : ℝ)] ![(43870825918519/100000000000000 : ℝ), (13416507921651/100000000000000 : ℝ), (10678166537029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534995143/1000000000 : ℝ)|^1063 ≤ (43870825918519/100000000000000 : ℝ)^807
        have hw : |(534995143/1000000000 : ℝ)|=(534995143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088173631/5000000000 : ℝ)|^1063 ≤ (13416507921651/100000000000000 : ℝ)^807
        have hw : |(-1088173631/5000000000 : ℝ)|=(1088173631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524238509/1000000000 : ℝ)|^1063 ≤ (10678166537029/25000000000000 : ℝ)^807
        have hw : |(524238509/1000000000 : ℝ)|=(524238509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349951431/10000000000 : ℝ)*x 0 + (524238509/1000000000 : ℝ)*x 1 + (-108817363/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349951431/10000000000 : ℝ)^1063 ≤ (43870825929321/100000000000000 : ℝ)^807 := by
    have hnat : (5349951431 : ℕ)^1063*100000000000000^807 ≤ 43870825929321^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349951431 10000000000 43870825929321 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524238509/1000000000 : ℝ)^1063 ≤ (10678166537029/25000000000000 : ℝ)^807 := by
    have hnat : (524238509 : ℕ)^1063*25000000000000^807 ≤ 10678166537029^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524238509 1000000000 10678166537029 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108817363/500000000 : ℝ)^1063 ≤ (13416507905411/100000000000000 : ℝ)^807 := by
    have hnat : (108817363 : ℕ)^1063*100000000000000^807 ≤ 13416507905411^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108817363 500000000 13416507905411 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349951431/10000000000 : ℝ), (524238509/1000000000 : ℝ), (-108817363/500000000 : ℝ)] ![(43870825929321/100000000000000 : ℝ), (10678166537029/25000000000000 : ℝ), (13416507905411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349951431/10000000000 : ℝ)|^1063 ≤ (43870825929321/100000000000000 : ℝ)^807
        have hw : |(5349951431/10000000000 : ℝ)|=(5349951431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524238509/1000000000 : ℝ)|^1063 ≤ (10678166537029/25000000000000 : ℝ)^807
        have hw : |(524238509/1000000000 : ℝ)|=(524238509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108817363/500000000 : ℝ)|^1063 ≤ (13416507905411/100000000000000 : ℝ)^807
        have hw : |(-108817363/500000000 : ℝ)|=(108817363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (867964379/2000000000 : ℝ)*x 0 + (4165028063/10000000000 : ℝ)*x 1 + (4521617449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867964379/2000000000 : ℝ)^1063 ≤ (33301913653983/100000000000000 : ℝ)^807 := by
    have hnat : (867964379 : ℕ)^1063*100000000000000^807 ≤ 33301913653983^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867964379 2000000000 33301913653983 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4165028063/10000000000 : ℝ)^1063 ≤ (3943315396227/12500000000000 : ℝ)^807 := by
    have hnat : (4165028063 : ℕ)^1063*12500000000000^807 ≤ 3943315396227^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165028063 10000000000 3943315396227 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521617449/10000000000 : ℝ)^1063 ≤ (7030312632959/20000000000000 : ℝ)^807 := by
    have hnat : (4521617449 : ℕ)^1063*20000000000000^807 ≤ 7030312632959^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521617449 10000000000 7030312632959 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867964379/2000000000 : ℝ), (4165028063/10000000000 : ℝ), (4521617449/10000000000 : ℝ)] ![(33301913653983/100000000000000 : ℝ), (3943315396227/12500000000000 : ℝ), (7030312632959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867964379/2000000000 : ℝ)|^1063 ≤ (33301913653983/100000000000000 : ℝ)^807
        have hw : |(867964379/2000000000 : ℝ)|=(867964379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4165028063/10000000000 : ℝ)|^1063 ≤ (3943315396227/12500000000000 : ℝ)^807
        have hw : |(4165028063/10000000000 : ℝ)|=(4165028063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521617449/10000000000 : ℝ)|^1063 ≤ (7030312632959/20000000000000 : ℝ)^807
        have hw : |(4521617449/10000000000 : ℝ)|=(4521617449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087905471/10000000000 : ℝ)*x 0 + (5243007987/10000000000 : ℝ)*x 1 + (5415261759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087905471/10000000000 : ℝ)^1063 ≤ (6351504207331/50000000000000 : ℝ)^807 := by
    have hnat : (2087905471 : ℕ)^1063*50000000000000^807 ≤ 6351504207331^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087905471 10000000000 6351504207331 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243007987/10000000000 : ℝ)^1063 ≤ (21359675654897/50000000000000 : ℝ)^807 := by
    have hnat : (5243007987 : ℕ)^1063*50000000000000^807 ≤ 21359675654897^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243007987 10000000000 21359675654897 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415261759/10000000000 : ℝ)^1063 ≤ (44577640264911/100000000000000 : ℝ)^807 := by
    have hnat : (5415261759 : ℕ)^1063*100000000000000^807 ≤ 44577640264911^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415261759 10000000000 44577640264911 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087905471/10000000000 : ℝ), (5243007987/10000000000 : ℝ), (5415261759/10000000000 : ℝ)] ![(6351504207331/50000000000000 : ℝ), (21359675654897/50000000000000 : ℝ), (44577640264911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087905471/10000000000 : ℝ)|^1063 ≤ (6351504207331/50000000000000 : ℝ)^807
        have hw : |(-2087905471/10000000000 : ℝ)|=(2087905471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243007987/10000000000 : ℝ)|^1063 ≤ (21359675654897/50000000000000 : ℝ)^807
        have hw : |(5243007987/10000000000 : ℝ)|=(5243007987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415261759/10000000000 : ℝ)|^1063 ≤ (44577640264911/100000000000000 : ℝ)^807
        have hw : |(5415261759/10000000000 : ℝ)|=(5415261759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305530171/10000000000 : ℝ)*x 0 + (-7826057/39062500 : ℝ)*x 1 + (5415261761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305530171/10000000000 : ℝ)^1063 ≤ (10847910248471/25000000000000 : ℝ)^807 := by
    have hnat : (5305530171 : ℕ)^1063*25000000000000^807 ≤ 10847910248471^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305530171 10000000000 10847910248471 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7826057/39062500 : ℝ)^1063 ≤ (751919919577/6250000000000 : ℝ)^807 := by
    have hnat : (7826057 : ℕ)^1063*6250000000000^807 ≤ 751919919577^807*39062500^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7826057 39062500 751919919577 6250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415261761/10000000000 : ℝ)^1063 ≤ (44577640286597/100000000000000 : ℝ)^807 := by
    have hnat : (5415261761 : ℕ)^1063*100000000000000^807 ≤ 44577640286597^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415261761 10000000000 44577640286597 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305530171/10000000000 : ℝ), (-7826057/39062500 : ℝ), (5415261761/10000000000 : ℝ)] ![(10847910248471/25000000000000 : ℝ), (751919919577/6250000000000 : ℝ), (44577640286597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305530171/10000000000 : ℝ)|^1063 ≤ (10847910248471/25000000000000 : ℝ)^807
        have hw : |(5305530171/10000000000 : ℝ)|=(5305530171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7826057/39062500 : ℝ)|^1063 ≤ (751919919577/6250000000000 : ℝ)^807
        have hw : |(-7826057/39062500 : ℝ)|=(7826057/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415261761/10000000000 : ℝ)|^1063 ≤ (44577640286597/100000000000000 : ℝ)^807
        have hw : |(5415261761/10000000000 : ℝ)|=(5415261761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305530173/10000000000 : ℝ)*x 0 + (16922693/31250000 : ℝ)*x 1 + (-200347059/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305530173/10000000000 : ℝ)^1063 ≤ (4339164101543/10000000000000 : ℝ)^807 := by
    have hnat : (5305530173 : ℕ)^1063*10000000000000^807 ≤ 4339164101543^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305530173 10000000000 4339164101543 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16922693/31250000 : ℝ)^1063 ≤ (22288820137877/50000000000000 : ℝ)^807 := by
    have hnat : (16922693 : ℕ)^1063*50000000000000^807 ≤ 22288820137877^807*31250000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16922693 31250000 22288820137877 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200347059/1000000000 : ℝ)^1063 ≤ (3007679674353/25000000000000 : ℝ)^807 := by
    have hnat : (200347059 : ℕ)^1063*25000000000000^807 ≤ 3007679674353^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200347059 1000000000 3007679674353 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305530173/10000000000 : ℝ), (16922693/31250000 : ℝ), (-200347059/1000000000 : ℝ)] ![(4339164101543/10000000000000 : ℝ), (22288820137877/50000000000000 : ℝ), (3007679674353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305530173/10000000000 : ℝ)|^1063 ≤ (4339164101543/10000000000000 : ℝ)^807
        have hw : |(5305530173/10000000000 : ℝ)|=(5305530173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16922693/31250000 : ℝ)|^1063 ≤ (22288820137877/50000000000000 : ℝ)^807
        have hw : |(16922693/31250000 : ℝ)|=(16922693/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200347059/1000000000 : ℝ)|^1063 ≤ (3007679674353/25000000000000 : ℝ)^807
        have hw : |(-200347059/1000000000 : ℝ)|=(200347059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s5_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4339848593/10000000000 : ℝ)*x 0 + (1130084313/2500000000 : ℝ)*x 1 + (4166314889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339848593/10000000000 : ℝ)^1063 ≤ (33302183512523/100000000000000 : ℝ)^807 := by
    have hnat : (4339848593 : ℕ)^1063*100000000000000^807 ≤ 33302183512523^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339848593 10000000000 33302183512523 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130084313/2500000000 : ℝ)^1063 ≤ (35138454216317/100000000000000 : ℝ)^807 := by
    have hnat : (1130084313 : ℕ)^1063*100000000000000^807 ≤ 35138454216317^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130084313 2500000000 35138454216317 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166314889/10000000000 : ℝ)^1063 ≤ (6311872452931/20000000000000 : ℝ)^807 := by
    have hnat : (4166314889 : ℕ)^1063*20000000000000^807 ≤ 6311872452931^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166314889 10000000000 6311872452931 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339848593/10000000000 : ℝ), (1130084313/2500000000 : ℝ), (4166314889/10000000000 : ℝ)] ![(33302183512523/100000000000000 : ℝ), (35138454216317/100000000000000 : ℝ), (6311872452931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339848593/10000000000 : ℝ)|^1063 ≤ (33302183512523/100000000000000 : ℝ)^807
        have hw : |(4339848593/10000000000 : ℝ)|=(4339848593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130084313/2500000000 : ℝ)|^1063 ≤ (35138454216317/100000000000000 : ℝ)^807
        have hw : |(1130084313/2500000000 : ℝ)|=(1130084313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166314889/10000000000 : ℝ)|^1063 ≤ (6311872452931/20000000000000 : ℝ)^807
        have hw : |(4166314889/10000000000 : ℝ)|=(4166314889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2191/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5507/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2191/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2191/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2191/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2191/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2191/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2191/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2191/20000 : ℝ) ^ (4251/1024 : ℝ) ≤ (322053761976341/3125000000000000000 : ℝ) := by
    have hpowers : (2191/20000 : ℝ)^4251 ≤ (322053761976341/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2191 : ℕ)^4251*3125000000000000000^1024 ≤ 322053761976341^1024*20000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2191 20000 322053761976341 3125000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2191/20000 : ℝ)) (X := (322053761976341/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4251/1024 : ℝ) ≤ (7085662506052641/20000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4251 ≤ (7085662506052641/20000000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4251*20000000000000000000^1024 ≤ 7085662506052641^1024*400^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 7085662506052641 20000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (7085662506052641/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562822053761976341/1562500000000000000 : ℝ) ≤ (625031028676141/625000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (1562822053761976341/1562500000000000000 : ℝ)^1024 ≤ (625031028676141/625000000000000 : ℝ)^4251 := by
      have hnat : (1562822053761976341 : ℕ)^1024*625000000000000^4251 ≤ 625031028676141^4251*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562822053761976341 1562500000000000000 625031028676141 625000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625031028676141/625000000000000 : ℝ)) (X := (1562822053761976341/1562500000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045734032913506117/100000000000000000000 : ℝ) ≤ (2000220294154383/2000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (100045734032913506117/100000000000000000000 : ℝ)^1024 ≤ (2000220294154383/2000000000000000 : ℝ)^4251 := by
      have hnat : (100045734032913506117 : ℕ)^1024*2000000000000000^4251 ≤ 2000220294154383^4251*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045734032913506117 100000000000000000000 2000220294154383 2000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000220294154383/2000000000000000 : ℝ)) (X := (100045734032913506117/100000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007085662506052641/10000000000000000000 : ℝ) ≤ (5000853241362787/5000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (10007085662506052641/10000000000000000000 : ℝ)^1024 ≤ (5000853241362787/5000000000000000 : ℝ)^4251 := by
      have hnat : (10007085662506052641 : ℕ)^1024*5000000000000000^4251 ≤ 5000853241362787^4251*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007085662506052641 10000000000000000000 5000853241362787 5000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000853241362787/5000000000000000 : ℝ)) (X := (10007085662506052641/10000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(322053761976341/3125000000000000000 : ℝ) ≤ ((3793862824931061283/3795000000000000000 : ℝ)+2*(605011953659/379500000000000 : ℝ)*(2191/20000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (3793862824931061283/3795000000000000000 : ℝ)+2*(605011953659/379500000000000 : ℝ)*(2191/20000 : ℝ)=(625031028676141/625000000000000 : ℝ) by norm_num, show 1+2*(322053761976341/3125000000000000000 : ℝ)=(1562822053761976341/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7085662506052641/20000000000000000000 : ℝ)+(322053761976341/3125000000000000000 : ℝ) ≤ ((3793862824931061283/3795000000000000000 : ℝ)+(605011953659/379500000000000 : ℝ)*((59/400 : ℝ)+(2191/20000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (3793862824931061283/3795000000000000000 : ℝ)+(605011953659/379500000000000 : ℝ)*((59/400 : ℝ)+(2191/20000 : ℝ))=(2000220294154383/2000000000000000 : ℝ) by norm_num, show 1+(7085662506052641/20000000000000000000 : ℝ)+(322053761976341/3125000000000000000 : ℝ)=(100045734032913506117/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7085662506052641/20000000000000000000 : ℝ) ≤ ((3793862824931061283/3795000000000000000 : ℝ)+2*(605011953659/379500000000000 : ℝ)*(59/400 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (3793862824931061283/3795000000000000000 : ℝ)+2*(605011953659/379500000000000 : ℝ)*(59/400 : ℝ)=(5000853241362787/5000000000000000 : ℝ) by norm_num, show 1+2*(7085662506052641/20000000000000000000 : ℝ)=(10007085662506052641/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3793862824931061283/3795000000000000000 : ℝ)*(X 1 0+X 2 0)+(605011953659/379500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (2191/20000 : ℝ)) (hi := (59/400 : ℝ)) (c := (3793862824931061283/3795000000000000000 : ℝ)) (alpha := (605011953659/379500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3793862824931061283/3795000000000000000 : ℝ)*(X 0 1+X 2 1)+(605011953659/379500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (2191/20000 : ℝ)) (hi := (59/400 : ℝ)) (c := (3793862824931061283/3795000000000000000 : ℝ)) (alpha := (605011953659/379500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3793862824931061283/3795000000000000000 : ℝ)*(X 0 2+X 1 2)+(605011953659/379500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (2191/20000 : ℝ)) (hi := (59/400 : ℝ)) (c := (3793862824931061283/3795000000000000000 : ℝ)) (alpha := (605011953659/379500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2087892479/10000000000 : ℝ)*X 0 0+(5415887881/10000000000 : ℝ)*X 0 1+(5242385089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534995143/1000000000 : ℝ)*X 1 0+(-1088173631/5000000000 : ℝ)*X 1 1+(524238509/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349951431/10000000000 : ℝ)*X 2 0+(524238509/1000000000 : ℝ)*X 2 1+(-108817363/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867964379/2000000000 : ℝ)*X 0 0+(4165028063/10000000000 : ℝ)*X 0 1+(4521617449/10000000000 : ℝ)*X 0 2+(867964379/2000000000 : ℝ)*X 1 0+(4165028063/10000000000 : ℝ)*X 1 1+(4521617449/10000000000 : ℝ)*X 1 2+(867964379/2000000000 : ℝ)*X 2 0+(4165028063/10000000000 : ℝ)*X 2 1+(4521617449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2087905471/10000000000 : ℝ)*X 0 0+(5243007987/10000000000 : ℝ)*X 0 1+(5415261759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305530171/10000000000 : ℝ)*X 1 0+(-7826057/39062500 : ℝ)*X 1 1+(5415261761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305530173/10000000000 : ℝ)*X 2 0+(16922693/31250000 : ℝ)*X 2 1+(-200347059/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339848593/10000000000 : ℝ)*X 0 0+(1130084313/2500000000 : ℝ)*X 0 1+(4166314889/10000000000 : ℝ)*X 0 2+(4339848593/10000000000 : ℝ)*X 1 0+(1130084313/2500000000 : ℝ)*X 1 1+(4166314889/10000000000 : ℝ)*X 1 2+(4339848593/10000000000 : ℝ)*X 2 0+(1130084313/2500000000 : ℝ)*X 2 1+(4166314889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30842788569672005747854653/2875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2056034859/100000000000000 : ℝ)*(base19) + (1916349743/100000000000000 : ℝ)*(base23) + (37653613/50000000000000 : ℝ)*(lower2) + (54083479/20000000000000 : ℝ)*(upper3) + (33566297/20000000000000 : ℝ)*(upper5) + (2142016736516767/50000000000000 : ℝ)*(major0) + (2142016736516767/50000000000000 : ℝ)*(major1) + (2142016736516767/50000000000000 : ℝ)*(major2) + (5763638772916447/100000000000000 : ℝ)*(sp0) + (5763677690668383/100000000000000 : ℝ)*(sp1) + (2881838915176749/50000000000000 : ℝ)*(sp2) + (2804365289357267/100000000000000 : ℝ)*(sp3) + (8194757359/20000000000000 : ℝ)*(sp4) + (10776204499/50000000000000 : ℝ)*(sp7) + (350548355220783/12500000000000 : ℝ)*(f.failure) + (2881839873351621/50000000000000 : ℝ)*(f.sum) + (6683659919779/1725000000000000000000000000 : ℝ)*base66 + (142896893815884483/5750000000000000000000000000000 : ℝ)*base68 + (31071276213884483/5750000000000000000000000000000 : ℝ)*base70 + (38954435225884483/5750000000000000000000000000000 : ℝ)*base72 + (6537581313529/1725000000000000000000000000 : ℝ)*base74 + (100044126335384483/5750000000000000000000000000000 : ℝ)*base76 + (30756763426884483/5750000000000000000000000000000 : ℝ)*base78 + (69248216316884483/5750000000000000000000000000000 : ℝ)*base80 + (410463516679/1725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8484403/1250000000000000000000 : ℝ)*base90 + (8484403/1250000000000000000000 : ℝ)*base92 + (8484403/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4300281934093483324227/1581250000000000000000000000 : ℝ) := by norm_num
    linear_combination (240058421/50000000000000 : ℝ)*(base19) + (10483489/2000000000000 : ℝ)*(base23) + (7000141/12500000000000 : ℝ)*(upper3) + (927181/5000000000000 : ℝ)*(lower4) + (54837621/100000000000000 : ℝ)*(upper5) + (2157517012778423/50000000000000 : ℝ)*(major0) + (2157517012778423/50000000000000 : ℝ)*(major1) + (2157517012778423/50000000000000 : ℝ)*(major2) + (2390156987/25000000000000 : ℝ)*(sp1) + (2596713551/25000000000000 : ℝ)*(sp2) + (2902693866735587/50000000000000 : ℝ)*(sp4) + (362836105795399/6250000000000 : ℝ)*(sp5) + (145134420561063/2500000000000 : ℝ)*(sp6) + (353085028373873/12500000000000 : ℝ)*(sp7) + (353085028373873/12500000000000 : ℝ)*(f.failure) + (2902693866735587/50000000000000 : ℝ)*(f.sum) + (11819210113933/2371875000000000000000000000 : ℝ)*base65 + (123097618482388903/63250000000000000000000000000000 : ℝ)*base67 + (478917252630388903/63250000000000000000000000000000 : ℝ)*base69 + (43678723475111097/63250000000000000000000000000000 : ℝ)*base72 + (27868587070057/9487500000000000000000000000 : ℝ)*base73 + (17750999103111097/63250000000000000000000000000000 : ℝ)*base76 + (425457278160111097/63250000000000000000000000000000 : ℝ)*base78 + (319730051990888903/63250000000000000000000000000000 : ℝ)*base79 + (46262623119457/9487500000000000000000000000 : ℝ)*base81 + (11509907/1250000000000000000000 : ℝ)*base89 + (11509907/1250000000000000000000 : ℝ)*base91 + (11509907/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1292_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2191/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1292_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1292_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1292_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1292_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1292_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

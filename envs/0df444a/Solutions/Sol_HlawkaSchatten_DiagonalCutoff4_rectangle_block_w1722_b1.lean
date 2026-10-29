-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1722_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:15.99895+00:00
-- url     : https://prove2.me/submissions/e64a1c69-f25d-4806-a3e5-e7e4b4297de4

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
theorem support_rectangle_w1722_s3_0 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1369874971/10000000000 : ℝ)*x 0 + (1092494261/2000000000 : ℝ)*x 1 + (1027926709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369874971/10000000000 : ℝ)^5399 ≤ (537644185497/6250000000000 : ℝ)^4375 := by
    have hnat : (1369874971 : ℕ)^5399*6250000000000^4375 ≤ 537644185497^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369874971 10000000000 537644185497 6250000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092494261/2000000000 : ℝ)^5399 ≤ (4741581586601/10000000000000 : ℝ)^4375 := by
    have hnat : (1092494261 : ℕ)^5399*10000000000000^4375 ≤ 4741581586601^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092494261 2000000000 4741581586601 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027926709/2000000000 : ℝ)^5399 ≤ (8796375428681/20000000000000 : ℝ)^4375 := by
    have hnat : (1027926709 : ℕ)^5399*20000000000000^4375 ≤ 8796375428681^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027926709 2000000000 8796375428681 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1369874971/10000000000 : ℝ), (1092494261/2000000000 : ℝ), (1027926709/2000000000 : ℝ)] ![(537644185497/6250000000000 : ℝ), (4741581586601/10000000000000 : ℝ), (8796375428681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1369874971/10000000000 : ℝ)|^5399 ≤ (537644185497/6250000000000 : ℝ)^4375
        have hw : |(-1369874971/10000000000 : ℝ)|=(1369874971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092494261/2000000000 : ℝ)|^5399 ≤ (4741581586601/10000000000000 : ℝ)^4375
        have hw : |(1092494261/2000000000 : ℝ)|=(1092494261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027926709/2000000000 : ℝ)|^5399 ≤ (8796375428681/20000000000000 : ℝ)^4375
        have hw : |(1027926709/2000000000 : ℝ)|=(1027926709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_1 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339482123/10000000000 : ℝ)*x 0 + (-1537112837/10000000000 : ℝ)*x 1 + (2569816773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339482123/10000000000 : ℝ)^5399 ≤ (2305092553011/5000000000000 : ℝ)^4375 := by
    have hnat : (5339482123 : ℕ)^5399*5000000000000^4375 ≤ 2305092553011^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339482123 10000000000 2305092553011 5000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537112837/10000000000 : ℝ)^5399 ≤ (4958135887641/50000000000000 : ℝ)^4375 := by
    have hnat : (1537112837 : ℕ)^5399*50000000000000^4375 ≤ 4958135887641^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537112837 10000000000 4958135887641 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569816773/5000000000 : ℝ)^5399 ≤ (21990938576983/50000000000000 : ℝ)^4375 := by
    have hnat : (2569816773 : ℕ)^5399*50000000000000^4375 ≤ 21990938576983^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569816773 5000000000 21990938576983 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339482123/10000000000 : ℝ), (-1537112837/10000000000 : ℝ), (2569816773/5000000000 : ℝ)] ![(2305092553011/5000000000000 : ℝ), (4958135887641/50000000000000 : ℝ), (21990938576983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339482123/10000000000 : ℝ)|^5399 ≤ (2305092553011/5000000000000 : ℝ)^4375
        have hw : |(5339482123/10000000000 : ℝ)|=(5339482123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1537112837/10000000000 : ℝ)|^5399 ≤ (4958135887641/50000000000000 : ℝ)^4375
        have hw : |(-1537112837/10000000000 : ℝ)|=(1537112837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569816773/5000000000 : ℝ)|^5399 ≤ (21990938576983/50000000000000 : ℝ)^4375
        have hw : |(2569816773/5000000000 : ℝ)|=(2569816773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_2 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334870531/2500000000 : ℝ)*x 0 + (2569816773/5000000000 : ℝ)*x 1 + (-384278209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334870531/2500000000 : ℝ)^5399 ≤ (368814808567/800000000000 : ℝ)^4375 := by
    have hnat : (1334870531 : ℕ)^5399*800000000000^4375 ≤ 368814808567^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334870531 2500000000 368814808567 800000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569816773/5000000000 : ℝ)^5399 ≤ (21990938576983/50000000000000 : ℝ)^4375 := by
    have hnat : (2569816773 : ℕ)^5399*50000000000000^4375 ≤ 21990938576983^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569816773 5000000000 21990938576983 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384278209/2500000000 : ℝ)^5399 ≤ (247906794183/2500000000000 : ℝ)^4375 := by
    have hnat : (384278209 : ℕ)^5399*2500000000000^4375 ≤ 247906794183^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384278209 2500000000 247906794183 2500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334870531/2500000000 : ℝ), (2569816773/5000000000 : ℝ), (-384278209/2500000000 : ℝ)] ![(368814808567/800000000000 : ℝ), (21990938576983/50000000000000 : ℝ), (247906794183/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334870531/2500000000 : ℝ)|^5399 ≤ (368814808567/800000000000 : ℝ)^4375
        have hw : |(1334870531/2500000000 : ℝ)|=(1334870531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569816773/5000000000 : ℝ)|^5399 ≤ (21990938576983/50000000000000 : ℝ)^4375
        have hw : |(2569816773/5000000000 : ℝ)|=(2569816773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384278209/2500000000 : ℝ)|^5399 ≤ (247906794183/2500000000000 : ℝ)^4375
        have hw : |(-384278209/2500000000 : ℝ)|=(384278209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_3 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (63899963/156250000 : ℝ)*x 0 + (906527169/2500000000 : ℝ)*x 1 + (2293876439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63899963/156250000 : ℝ)^5399 ≤ (6634705382103/20000000000000 : ℝ)^4375 := by
    have hnat : (63899963 : ℕ)^5399*20000000000000^4375 ≤ 6634705382103^4375*156250000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63899963 156250000 6634705382103 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906527169/2500000000 : ℝ)^5399 ≤ (5719456848499/20000000000000 : ℝ)^4375 := by
    have hnat : (906527169 : ℕ)^5399*20000000000000^4375 ≤ 5719456848499^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906527169 2500000000 5719456848499 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293876439/5000000000 : ℝ)^5399 ≤ (9557297207889/25000000000000 : ℝ)^4375 := by
    have hnat : (2293876439 : ℕ)^5399*25000000000000^4375 ≤ 9557297207889^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293876439 5000000000 9557297207889 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63899963/156250000 : ℝ), (906527169/2500000000 : ℝ), (2293876439/5000000000 : ℝ)] ![(6634705382103/20000000000000 : ℝ), (5719456848499/20000000000000 : ℝ), (9557297207889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63899963/156250000 : ℝ)|^5399 ≤ (6634705382103/20000000000000 : ℝ)^4375
        have hw : |(63899963/156250000 : ℝ)|=(63899963/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906527169/2500000000 : ℝ)|^5399 ≤ (5719456848499/20000000000000 : ℝ)^4375
        have hw : |(906527169/2500000000 : ℝ)|=(906527169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2293876439/5000000000 : ℝ)|^5399 ≤ (9557297207889/25000000000000 : ℝ)^4375
        have hw : |(2293876439/5000000000 : ℝ)|=(2293876439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_4 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1370019213/10000000000 : ℝ)*x 0 + (5143246303/10000000000 : ℝ)*x 1 + (1364701191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370019213/10000000000 : ℝ)^5399 ≤ (4301712386881/50000000000000 : ℝ)^4375 := by
    have hnat : (1370019213 : ℕ)^5399*50000000000000^4375 ≤ 4301712386881^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370019213 10000000000 4301712386881 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143246303/10000000000 : ℝ)^5399 ≤ (11005008036021/25000000000000 : ℝ)^4375 := by
    have hnat : (5143246303 : ℕ)^5399*25000000000000^4375 ≤ 11005008036021^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143246303 10000000000 11005008036021 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364701191/2500000000 : ℝ)^5399 ≤ (11844135769057/25000000000000 : ℝ)^4375 := by
    have hnat : (1364701191 : ℕ)^5399*25000000000000^4375 ≤ 11844135769057^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364701191 2500000000 11844135769057 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1370019213/10000000000 : ℝ), (5143246303/10000000000 : ℝ), (1364701191/2500000000 : ℝ)] ![(4301712386881/50000000000000 : ℝ), (11005008036021/25000000000000 : ℝ), (11844135769057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1370019213/10000000000 : ℝ)|^5399 ≤ (4301712386881/50000000000000 : ℝ)^4375
        have hw : |(-1370019213/10000000000 : ℝ)|=(1370019213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143246303/10000000000 : ℝ)|^5399 ≤ (11005008036021/25000000000000 : ℝ)^4375
        have hw : |(5143246303/10000000000 : ℝ)|=(5143246303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364701191/2500000000 : ℝ)|^5399 ≤ (11844135769057/25000000000000 : ℝ)^4375
        have hw : |(1364701191/2500000000 : ℝ)|=(1364701191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_5 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313265833/2500000000 : ℝ)*x 0 + (-608970809/5000000000 : ℝ)*x 1 + (1364701191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313265833/2500000000 : ℝ)^5399 ≤ (45182807959341/100000000000000 : ℝ)^4375 := by
    have hnat : (1313265833 : ℕ)^5399*100000000000000^4375 ≤ 45182807959341^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313265833 2500000000 45182807959341 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608970809/5000000000 : ℝ)^5399 ≤ (7440648953073/100000000000000 : ℝ)^4375 := by
    have hnat : (608970809 : ℕ)^5399*100000000000000^4375 ≤ 7440648953073^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608970809 5000000000 7440648953073 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364701191/2500000000 : ℝ)^5399 ≤ (11844135769057/25000000000000 : ℝ)^4375 := by
    have hnat : (1364701191 : ℕ)^5399*25000000000000^4375 ≤ 11844135769057^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364701191 2500000000 11844135769057 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313265833/2500000000 : ℝ), (-608970809/5000000000 : ℝ), (1364701191/2500000000 : ℝ)] ![(45182807959341/100000000000000 : ℝ), (7440648953073/100000000000000 : ℝ), (11844135769057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313265833/2500000000 : ℝ)|^5399 ≤ (45182807959341/100000000000000 : ℝ)^4375
        have hw : |(1313265833/2500000000 : ℝ)|=(1313265833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608970809/5000000000 : ℝ)|^5399 ≤ (7440648953073/100000000000000 : ℝ)^4375
        have hw : |(-608970809/5000000000 : ℝ)|=(608970809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364701191/2500000000 : ℝ)|^5399 ≤ (11844135769057/25000000000000 : ℝ)^4375
        have hw : |(1364701191/2500000000 : ℝ)|=(1364701191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_6 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313265833/2500000000 : ℝ)*x 0 + (1364701191/2500000000 : ℝ)*x 1 + (-608970809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313265833/2500000000 : ℝ)^5399 ≤ (45182807959341/100000000000000 : ℝ)^4375 := by
    have hnat : (1313265833 : ℕ)^5399*100000000000000^4375 ≤ 45182807959341^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313265833 2500000000 45182807959341 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364701191/2500000000 : ℝ)^5399 ≤ (11844135769057/25000000000000 : ℝ)^4375 := by
    have hnat : (1364701191 : ℕ)^5399*25000000000000^4375 ≤ 11844135769057^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364701191 2500000000 11844135769057 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608970809/5000000000 : ℝ)^5399 ≤ (7440648953073/100000000000000 : ℝ)^4375 := by
    have hnat : (608970809 : ℕ)^5399*100000000000000^4375 ≤ 7440648953073^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608970809 5000000000 7440648953073 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313265833/2500000000 : ℝ), (1364701191/2500000000 : ℝ), (-608970809/5000000000 : ℝ)] ![(45182807959341/100000000000000 : ℝ), (11844135769057/25000000000000 : ℝ), (7440648953073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313265833/2500000000 : ℝ)|^5399 ≤ (45182807959341/100000000000000 : ℝ)^4375
        have hw : |(1313265833/2500000000 : ℝ)|=(1313265833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364701191/2500000000 : ℝ)|^5399 ≤ (11844135769057/25000000000000 : ℝ)^4375
        have hw : |(1364701191/2500000000 : ℝ)|=(1364701191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-608970809/5000000000 : ℝ)|^5399 ≤ (7440648953073/100000000000000 : ℝ)^4375
        have hw : |(-608970809/5000000000 : ℝ)|=(608970809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s3_7 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511253411/1250000000 : ℝ)*x 0 + (1144247869/2500000000 : ℝ)*x 1 + (3637030287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511253411/1250000000 : ℝ)^5399 ≤ (8294456985339/25000000000000 : ℝ)^4375 := by
    have hnat : (511253411 : ℕ)^5399*25000000000000^4375 ≤ 8294456985339^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511253411 1250000000 8294456985339 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144247869/2500000000 : ℝ)^5399 ≤ (1905927852767/5000000000000 : ℝ)^4375 := by
    have hnat : (1144247869 : ℕ)^5399*5000000000000^4375 ≤ 1905927852767^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144247869 2500000000 1905927852767 5000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3637030287/10000000000 : ℝ)^5399 ≤ (896987968591/3125000000000 : ℝ)^4375 := by
    have hnat : (3637030287 : ℕ)^5399*3125000000000^4375 ≤ 896987968591^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3637030287 10000000000 896987968591 3125000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511253411/1250000000 : ℝ), (1144247869/2500000000 : ℝ), (3637030287/10000000000 : ℝ)] ![(8294456985339/25000000000000 : ℝ), (1905927852767/5000000000000 : ℝ), (896987968591/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511253411/1250000000 : ℝ)|^5399 ≤ (8294456985339/25000000000000 : ℝ)^4375
        have hw : |(511253411/1250000000 : ℝ)|=(511253411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144247869/2500000000 : ℝ)|^5399 ≤ (1905927852767/5000000000000 : ℝ)^4375
        have hw : |(1144247869/2500000000 : ℝ)|=(1144247869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3637030287/10000000000 : ℝ)|^5399 ≤ (896987968591/3125000000000 : ℝ)^4375
        have hw : |(3637030287/10000000000 : ℝ)|=(3637030287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1722_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8507/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5047/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8507/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5047/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8507/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5047/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8507/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5047/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8507/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5047/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8507/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5047/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5047/50000 : ℝ) ^ (5391/1024 : ℝ) ≤ (571141095985627/100000000000000000000 : ℝ) := by
    have hpowers : (5047/50000 : ℝ)^5391 ≤ (571141095985627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5047 : ℕ)^5391*100000000000000000000^1024 ≤ 571141095985627^1024*50000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5047 50000 571141095985627 100000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5047/50000 : ℝ)) (X := (571141095985627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8507/50000 : ℝ) ^ (5391/1024 : ℝ) ≤ (1784416626467813/20000000000000000000 : ℝ) := by
    have hpowers : (8507/50000 : ℝ)^5391 ≤ (1784416626467813/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8507 : ℕ)^5391*20000000000000000000^1024 ≤ 1784416626467813^1024*50000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8507 50000 1784416626467813 20000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8507/50000 : ℝ)) (X := (1784416626467813/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000571141095985627/50000000000000000000 : ℝ) ≤ (5000010848558273/5000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (50000571141095985627/50000000000000000000 : ℝ)^1024 ≤ (5000010848558273/5000000000000000 : ℝ)^5391 := by
      have hnat : (50000571141095985627 : ℕ)^1024*5000000000000000^5391 ≤ 5000010848558273^5391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000571141095985627 50000000000000000000 5000010848558273 5000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010848558273/5000000000000000 : ℝ)) (X := (50000571141095985627/50000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002373306057081173/25000000000000000000 : ℝ) ≤ (5000090156630081/5000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (25002373306057081173/25000000000000000000 : ℝ)^1024 ≤ (5000090156630081/5000000000000000 : ℝ)^5391 := by
      have hnat : (25002373306057081173 : ℕ)^1024*5000000000000000^5391 ≤ 5000090156630081^5391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002373306057081173 25000000000000000000 5000090156630081 5000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000090156630081/5000000000000000 : ℝ)) (X := (25002373306057081173/25000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001784416626467813/10000000000000000000 : ℝ) ≤ (5000169464701889/5000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (10001784416626467813/10000000000000000000 : ℝ)^1024 ≤ (5000169464701889/5000000000000000 : ℝ)^5391 := by
      have hnat : (10001784416626467813 : ℕ)^1024*5000000000000000^5391 ≤ 5000169464701889^5391*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001784416626467813 10000000000000000000 5000169464701889 5000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000169464701889/5000000000000000 : ℝ)) (X := (10001784416626467813/10000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(571141095985627/100000000000000000000 : ℝ) ≤ ((4324809250083698657/4325000000000000000 : ℝ)+2*(619594311/2703125000000 : ℝ)*(5047/50000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (4324809250083698657/4325000000000000000 : ℝ)+2*(619594311/2703125000000 : ℝ)*(5047/50000 : ℝ)=(5000010848558273/5000000000000000 : ℝ) by norm_num, show 1+2*(571141095985627/100000000000000000000 : ℝ)=(50000571141095985627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1784416626467813/20000000000000000000 : ℝ)+(571141095985627/100000000000000000000 : ℝ) ≤ ((4324809250083698657/4325000000000000000 : ℝ)+(619594311/2703125000000 : ℝ)*((8507/50000 : ℝ)+(5047/50000 : ℝ)))^(5391/1024 : ℝ) := by
    rw [show (4324809250083698657/4325000000000000000 : ℝ)+(619594311/2703125000000 : ℝ)*((8507/50000 : ℝ)+(5047/50000 : ℝ))=(5000090156630081/5000000000000000 : ℝ) by norm_num, show 1+(1784416626467813/20000000000000000000 : ℝ)+(571141095985627/100000000000000000000 : ℝ)=(25002373306057081173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1784416626467813/20000000000000000000 : ℝ) ≤ ((4324809250083698657/4325000000000000000 : ℝ)+2*(619594311/2703125000000 : ℝ)*(8507/50000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (4324809250083698657/4325000000000000000 : ℝ)+2*(619594311/2703125000000 : ℝ)*(8507/50000 : ℝ)=(5000169464701889/5000000000000000 : ℝ) by norm_num, show 1+2*(1784416626467813/20000000000000000000 : ℝ)=(10001784416626467813/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4324809250083698657/4325000000000000000 : ℝ)*(X 1 0+X 2 0)+(619594311/2703125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (5047/50000 : ℝ)) (hi := (8507/50000 : ℝ)) (c := (4324809250083698657/4325000000000000000 : ℝ)) (alpha := (619594311/2703125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4324809250083698657/4325000000000000000 : ℝ)*(X 0 1+X 2 1)+(619594311/2703125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (5047/50000 : ℝ)) (hi := (8507/50000 : ℝ)) (c := (4324809250083698657/4325000000000000000 : ℝ)) (alpha := (619594311/2703125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4324809250083698657/4325000000000000000 : ℝ)*(X 0 2+X 1 2)+(619594311/2703125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (5047/50000 : ℝ)) (hi := (8507/50000 : ℝ)) (c := (4324809250083698657/4325000000000000000 : ℝ)) (alpha := (619594311/2703125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1369874971/10000000000 : ℝ)*X 0 0+(1092494261/2000000000 : ℝ)*X 0 1+(1027926709/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5339482123/10000000000 : ℝ)*X 1 0+(-1537112837/10000000000 : ℝ)*X 1 1+(2569816773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1334870531/2500000000 : ℝ)*X 2 0+(2569816773/5000000000 : ℝ)*X 2 1+(-384278209/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((63899963/156250000 : ℝ)*X 0 0+(906527169/2500000000 : ℝ)*X 0 1+(2293876439/5000000000 : ℝ)*X 0 2+(63899963/156250000 : ℝ)*X 1 0+(906527169/2500000000 : ℝ)*X 1 1+(2293876439/5000000000 : ℝ)*X 1 2+(63899963/156250000 : ℝ)*X 2 0+(906527169/2500000000 : ℝ)*X 2 1+(2293876439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1370019213/10000000000 : ℝ)*X 0 0+(5143246303/10000000000 : ℝ)*X 0 1+(1364701191/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313265833/2500000000 : ℝ)*X 1 0+(-608970809/5000000000 : ℝ)*X 1 1+(1364701191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313265833/2500000000 : ℝ)*X 2 0+(1364701191/2500000000 : ℝ)*X 2 1+(-608970809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((511253411/1250000000 : ℝ)*X 0 0+(1144247869/2500000000 : ℝ)*X 0 1+(3637030287/10000000000 : ℝ)*X 0 2+(511253411/1250000000 : ℝ)*X 1 0+(1144247869/2500000000 : ℝ)*X 1 1+(3637030287/10000000000 : ℝ)*X 1 2+(511253411/1250000000 : ℝ)*X 2 0+(1144247869/2500000000 : ℝ)*X 2 1+(3637030287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68077104350094665567011737/21625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57090219/12500000000000 : ℝ)*(base19) + (429900073/100000000000000 : ℝ)*(base23) + (7315571/50000000000000 : ℝ)*(lower2) + (15145893/20000000000000 : ℝ)*(upper3) + (57205267/100000000000000 : ℝ)*(upper5) + (206871461658049/10000000000000 : ℝ)*(major0) + (206871461658049/10000000000000 : ℝ)*(major1) + (206871461658049/10000000000000 : ℝ)*(major2) + (48398996136197/1562500000000 : ℝ)*(sp0) + (19359624300041/625000000000 : ℝ)*(sp1) + (1548769957414119/50000000000000 : ℝ)*(sp2) + (519943559166079/50000000000000 : ℝ)*(sp3) + (4592011703/100000000000000 : ℝ)*(sp4) + (832582349/50000000000000 : ℝ)*(sp7) + (129986097937107/12500000000000 : ℝ)*(f.failure) + (3097540344728311/100000000000000 : ℝ)*(f.sum) + (1814208022651/865000000000000000000000000 : ℝ)*base65 + (471809096864309807/43250000000000000000000000000000 : ℝ)*base68 + (308821168984559807/43250000000000000000000000000000 : ℝ)*base70 + (462437741143059807/43250000000000000000000000000000 : ℝ)*base72 + (76976762167/27031250000000000000000000 : ℝ)*base74 + (516788504555559807/43250000000000000000000000000000 : ℝ)*base76 + (34465610977059807/43250000000000000000000000000000 : ℝ)*base78 + (172019753946059807/43250000000000000000000000000000 : ℝ)*base80 + (1973590490183/432500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2284087/1250000000000000000000 : ℝ)*base89 + (2284087/1250000000000000000000 : ℝ)*base91 + (2284087/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (665916123389239103752057671/54062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (833068081/50000000000000 : ℝ)*(base19) + (896036101/50000000000000 : ℝ)*(base23) + (123653467/25000000000000 : ℝ)*(lower1) + (131005547/50000000000000 : ℝ)*(upper3) + (28203929/50000000000000 : ℝ)*(lower4) + (255788623/100000000000000 : ℝ)*(upper5) + (1058209267782299/50000000000000 : ℝ)*(major0) + (1058209267782299/50000000000000 : ℝ)*(major1) + (1058209267782299/50000000000000 : ℝ)*(major2) + (563946977/50000000000000 : ℝ)*(sp2) + (1584484181724673/50000000000000 : ℝ)*(sp4) + (99030209291037/3125000000000 : ℝ)*(sp5) + (316896544348319/10000000000000 : ℝ)*(sp6) + (531934148547849/50000000000000 : ℝ)*(sp7) + (531934148547849/50000000000000 : ℝ)*(f.failure) + (1584484181724673/50000000000000 : ℝ)*(f.sum) + (3865548801673/2162500000000000000000000000 : ℝ)*base65 + (796206262279572443/216250000000000000000000000000000 : ℝ)*base67 + (631650482239572443/216250000000000000000000000000000 : ℝ)*base69 + (37048460210842927557/216250000000000000000000000000000 : ℝ)*base72 + (3813612436887/540625000000000000000000000 : ℝ)*base73 + (4653527617069572443/216250000000000000000000000000000 : ℝ)*base75 + (2069543284377072443/216250000000000000000000000000000 : ℝ)*base77 + (2203424980232072443/216250000000000000000000000000000 : ℝ)*base79 + (5743926576177/2162500000000000000000000000 : ℝ)*base82 + (66089291/5000000000000000000000 : ℝ)*base90 + (66089291/5000000000000000000000 : ℝ)*base92 + (66089291/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1722_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1722_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1722_s4_0 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334869961/2500000000 : ℝ)*x 0 + (-1537105029/10000000000 : ℝ)*x 1 + (5139641731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334869961/2500000000 : ℝ)^5399 ≤ (23050913388709/50000000000000 : ℝ)^4375 := by
    have hnat : (1334869961 : ℕ)^5399*50000000000000^4375 ≤ 23050913388709^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334869961 2500000000 23050913388709 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537105029/10000000000 : ℝ)^5399 ≤ (4958104807177/50000000000000 : ℝ)^4375 := by
    have hnat : (1537105029 : ℕ)^5399*50000000000000^4375 ≤ 4958104807177^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537105029 10000000000 4958104807177 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139641731/10000000000 : ℝ)^5399 ≤ (43981963590161/100000000000000 : ℝ)^4375 := by
    have hnat : (5139641731 : ℕ)^5399*100000000000000^4375 ≤ 43981963590161^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139641731 10000000000 43981963590161 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334869961/2500000000 : ℝ), (-1537105029/10000000000 : ℝ), (5139641731/10000000000 : ℝ)] ![(23050913388709/50000000000000 : ℝ), (4958104807177/50000000000000 : ℝ), (43981963590161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334869961/2500000000 : ℝ)|^5399 ≤ (23050913388709/50000000000000 : ℝ)^4375
        have hw : |(1334869961/2500000000 : ℝ)|=(1334869961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1537105029/10000000000 : ℝ)|^5399 ≤ (4958104807177/50000000000000 : ℝ)^4375
        have hw : |(-1537105029/10000000000 : ℝ)|=(1537105029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139641731/10000000000 : ℝ)|^5399 ≤ (43981963590161/100000000000000 : ℝ)^4375
        have hw : |(5139641731/10000000000 : ℝ)|=(5139641731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_1 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089600317/10000000000 : ℝ)*x 0 + (906533941/2500000000 : ℝ)*x 1 + (1146931157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089600317/10000000000 : ℝ)^5399 ≤ (53077686061/160000000000 : ℝ)^4375 := by
    have hnat : (4089600317 : ℕ)^5399*160000000000^4375 ≤ 53077686061^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089600317 10000000000 53077686061 160000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906533941/2500000000 : ℝ)^5399 ≤ (571950957471/2000000000000 : ℝ)^4375 := by
    have hnat : (906533941 : ℕ)^5399*2000000000000^4375 ≤ 571950957471^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906533941 2500000000 571950957471 2000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146931157/2500000000 : ℝ)^5399 ≤ (38228898329991/100000000000000 : ℝ)^4375 := by
    have hnat : (1146931157 : ℕ)^5399*100000000000000^4375 ≤ 38228898329991^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146931157 2500000000 38228898329991 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089600317/10000000000 : ℝ), (906533941/2500000000 : ℝ), (1146931157/2500000000 : ℝ)] ![(53077686061/160000000000 : ℝ), (571950957471/2000000000000 : ℝ), (38228898329991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089600317/10000000000 : ℝ)|^5399 ≤ (53077686061/160000000000 : ℝ)^4375
        have hw : |(4089600317/10000000000 : ℝ)|=(4089600317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906533941/2500000000 : ℝ)|^5399 ≤ (571950957471/2000000000000 : ℝ)^4375
        have hw : |(906533941/2500000000 : ℝ)|=(906533941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146931157/2500000000 : ℝ)|^5399 ≤ (38228898329991/100000000000000 : ℝ)^4375
        have hw : |(1146931157/2500000000 : ℝ)|=(1146931157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_2 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1370022409/10000000000 : ℝ)*x 0 + (2571627233/5000000000 : ℝ)*x 1 + (6823493/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370022409/10000000000 : ℝ)^5399 ≤ (860344954153/10000000000000 : ℝ)^4375 := by
    have hnat : (1370022409 : ℕ)^5399*10000000000000^4375 ≤ 860344954153^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370022409 10000000000 860344954153 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571627233/5000000000 : ℝ)^5399 ≤ (44020118362131/100000000000000 : ℝ)^4375 := by
    have hnat : (2571627233 : ℕ)^5399*100000000000000^4375 ≤ 44020118362131^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571627233 5000000000 44020118362131 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6823493/12500000 : ℝ)^5399 ≤ (23688216037423/50000000000000 : ℝ)^4375 := by
    have hnat : (6823493 : ℕ)^5399*50000000000000^4375 ≤ 23688216037423^4375*12500000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6823493 12500000 23688216037423 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1370022409/10000000000 : ℝ), (2571627233/5000000000 : ℝ), (6823493/12500000 : ℝ)] ![(860344954153/10000000000000 : ℝ), (44020118362131/100000000000000 : ℝ), (23688216037423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1370022409/10000000000 : ℝ)|^5399 ≤ (860344954153/10000000000000 : ℝ)^4375
        have hw : |(-1370022409/10000000000 : ℝ)|=(1370022409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571627233/5000000000 : ℝ)|^5399 ≤ (44020118362131/100000000000000 : ℝ)^4375
        have hw : |(2571627233/5000000000 : ℝ)|=(2571627233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6823493/12500000 : ℝ)|^5399 ≤ (23688216037423/50000000000000 : ℝ)^4375
        have hw : |(6823493/12500000 : ℝ)|=(6823493/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_3 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626533313/5000000000 : ℝ)*x 0 + (-608975617/5000000000 : ℝ)*x 1 + (545879473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626533313/5000000000 : ℝ)^5399 ≤ (4518284292321/10000000000000 : ℝ)^4375 := by
    have hnat : (2626533313 : ℕ)^5399*10000000000000^4375 ≤ 4518284292321^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626533313 5000000000 4518284292321 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608975617/5000000000 : ℝ)^5399 ≤ (930090181143/12500000000000 : ℝ)^4375 := by
    have hnat : (608975617 : ℕ)^5399*12500000000000^4375 ≤ 930090181143^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608975617 5000000000 930090181143 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545879473/1000000000 : ℝ)^5399 ≤ (47376435609239/100000000000000 : ℝ)^4375 := by
    have hnat : (545879473 : ℕ)^5399*100000000000000^4375 ≤ 47376435609239^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545879473 1000000000 47376435609239 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626533313/5000000000 : ℝ), (-608975617/5000000000 : ℝ), (545879473/1000000000 : ℝ)] ![(4518284292321/10000000000000 : ℝ), (930090181143/12500000000000 : ℝ), (47376435609239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626533313/5000000000 : ℝ)|^5399 ≤ (4518284292321/10000000000000 : ℝ)^4375
        have hw : |(2626533313/5000000000 : ℝ)|=(2626533313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608975617/5000000000 : ℝ)|^5399 ≤ (930090181143/12500000000000 : ℝ)^4375
        have hw : |(-608975617/5000000000 : ℝ)|=(608975617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545879473/1000000000 : ℝ)|^5399 ≤ (47376435609239/100000000000000 : ℝ)^4375
        have hw : |(545879473/1000000000 : ℝ)|=(545879473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_4 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050613409/2000000000 : ℝ)*x 0 + (5458792329/10000000000 : ℝ)*x 1 + (-1217954057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050613409/2000000000 : ℝ)^5399 ≤ (5647855921331/12500000000000 : ℝ)^4375 := by
    have hnat : (1050613409 : ℕ)^5399*12500000000000^4375 ≤ 5647855921331^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050613409 2000000000 5647855921331 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458792329/10000000000 : ℝ)^5399 ≤ (9475281978771/20000000000000 : ℝ)^4375 := by
    have hnat : (5458792329 : ℕ)^5399*20000000000000^4375 ≤ 9475281978771^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458792329 10000000000 9475281978771 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217954057/10000000000 : ℝ)^5399 ≤ (3720371366037/50000000000000 : ℝ)^4375 := by
    have hnat : (1217954057 : ℕ)^5399*50000000000000^4375 ≤ 3720371366037^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217954057 10000000000 3720371366037 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050613409/2000000000 : ℝ), (5458792329/10000000000 : ℝ), (-1217954057/10000000000 : ℝ)] ![(5647855921331/12500000000000 : ℝ), (9475281978771/20000000000000 : ℝ), (3720371366037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050613409/2000000000 : ℝ)|^5399 ≤ (5647855921331/12500000000000 : ℝ)^4375
        have hw : |(1050613409/2000000000 : ℝ)|=(1050613409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458792329/10000000000 : ℝ)|^5399 ≤ (9475281978771/20000000000000 : ℝ)^4375
        have hw : |(5458792329/10000000000 : ℝ)|=(5458792329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217954057/10000000000 : ℝ)|^5399 ≤ (3720371366037/50000000000000 : ℝ)^4375
        have hw : |(-1217954057/10000000000 : ℝ)|=(1217954057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_5 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2045014917/5000000000 : ℝ)*x 0 + (915393019/2000000000 : ℝ)*x 1 + (909263877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045014917/5000000000 : ℝ)^5399 ≤ (8294463357041/25000000000000 : ℝ)^4375 := by
    have hnat : (2045014917 : ℕ)^5399*25000000000000^4375 ≤ 8294463357041^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045014917 5000000000 8294463357041 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915393019/2000000000 : ℝ)^5399 ≤ (7623657184443/20000000000000 : ℝ)^4375 := by
    have hnat : (915393019 : ℕ)^5399*20000000000000^4375 ≤ 7623657184443^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915393019 2000000000 7623657184443 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909263877/2500000000 : ℝ)^5399 ≤ (5740772125683/20000000000000 : ℝ)^4375 := by
    have hnat : (909263877 : ℕ)^5399*20000000000000^4375 ≤ 5740772125683^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909263877 2500000000 5740772125683 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2045014917/5000000000 : ℝ), (915393019/2000000000 : ℝ), (909263877/2500000000 : ℝ)] ![(8294463357041/25000000000000 : ℝ), (7623657184443/20000000000000 : ℝ), (5740772125683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2045014917/5000000000 : ℝ)|^5399 ≤ (8294463357041/25000000000000 : ℝ)^4375
        have hw : |(2045014917/5000000000 : ℝ)|=(2045014917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915393019/2000000000 : ℝ)|^5399 ≤ (7623657184443/20000000000000 : ℝ)^4375
        have hw : |(915393019/2000000000 : ℝ)|=(915393019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(909263877/2500000000 : ℝ)|^5399 ≤ (5740772125683/20000000000000 : ℝ)^4375
        have hw : |(909263877/2500000000 : ℝ)|=(909263877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_6 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22805261/5000000000 : ℝ)*x 0 + (1424059127/2500000000 : ℝ)*x 1 + (1424202793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22805261/5000000000 : ℝ)^5399 ≤ (16145909279/12500000000000 : ℝ)^4375 := by
    have hnat : (22805261 : ℕ)^5399*12500000000000^4375 ≤ 16145909279^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22805261 5000000000 16145909279 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424059127/2500000000 : ℝ)^5399 ≤ (49932308095037/100000000000000 : ℝ)^4375 := by
    have hnat : (1424059127 : ℕ)^5399*100000000000000^4375 ≤ 49932308095037^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424059127 2500000000 49932308095037 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424202793/2500000000 : ℝ)^5399 ≤ (49938524624803/100000000000000 : ℝ)^4375 := by
    have hnat : (1424202793 : ℕ)^5399*100000000000000^4375 ≤ 49938524624803^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424202793 2500000000 49938524624803 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22805261/5000000000 : ℝ), (1424059127/2500000000 : ℝ), (1424202793/2500000000 : ℝ)] ![(16145909279/12500000000000 : ℝ), (49932308095037/100000000000000 : ℝ), (49938524624803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22805261/5000000000 : ℝ)|^5399 ≤ (16145909279/12500000000000 : ℝ)^4375
        have hw : |(-22805261/5000000000 : ℝ)|=(22805261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424059127/2500000000 : ℝ)|^5399 ≤ (49932308095037/100000000000000 : ℝ)^4375
        have hw : |(1424059127/2500000000 : ℝ)|=(1424059127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1424202793/2500000000 : ℝ)|^5399 ≤ (49938524624803/100000000000000 : ℝ)^4375
        have hw : |(1424202793/2500000000 : ℝ)|=(1424202793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_7 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1364329683/10000000000 : ℝ)*x 0 + (-3088159583/10000000000 : ℝ)*x 1 + (1462934263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1364329683/10000000000 : ℝ)^5399 ≤ (2139838643363/25000000000000 : ℝ)^4375 := by
    have hnat : (1364329683 : ℕ)^5399*25000000000000^4375 ≤ 2139838643363^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364329683 10000000000 2139838643363 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3088159583/10000000000 : ℝ)^5399 ≤ (11728171743037/50000000000000 : ℝ)^4375 := by
    have hnat : (3088159583 : ℕ)^5399*50000000000000^4375 ≤ 11728171743037^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088159583 10000000000 11728171743037 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1462934263/2000000000 : ℝ)^5399 ≤ (33992150961243/50000000000000 : ℝ)^4375 := by
    have hnat : (1462934263 : ℕ)^5399*50000000000000^4375 ≤ 33992150961243^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462934263 2000000000 33992150961243 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1364329683/10000000000 : ℝ), (-3088159583/10000000000 : ℝ), (1462934263/2000000000 : ℝ)] ![(2139838643363/25000000000000 : ℝ), (11728171743037/50000000000000 : ℝ), (33992150961243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1364329683/10000000000 : ℝ)|^5399 ≤ (2139838643363/25000000000000 : ℝ)^4375
        have hw : |(1364329683/10000000000 : ℝ)|=(1364329683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3088159583/10000000000 : ℝ)|^5399 ≤ (11728171743037/50000000000000 : ℝ)^4375
        have hw : |(-3088159583/10000000000 : ℝ)|=(3088159583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1462934263/2000000000 : ℝ)|^5399 ≤ (33992150961243/50000000000000 : ℝ)^4375
        have hw : |(1462934263/2000000000 : ℝ)|=(1462934263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_8 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171275319/1000000000 : ℝ)*x 0 + (3980644221/5000000000 : ℝ)*x 1 + (-968526421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171275319/1000000000 : ℝ)^5399 ≤ (1133275698151/10000000000000 : ℝ)^4375 := by
    have hnat : (171275319 : ℕ)^5399*10000000000000^4375 ≤ 1133275698151^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171275319 1000000000 1133275698151 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3980644221/5000000000 : ℝ)^5399 ≤ (75475814224163/100000000000000 : ℝ)^4375 := by
    have hnat : (3980644221 : ℕ)^5399*100000000000000^4375 ≤ 75475814224163^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980644221 5000000000 75475814224163 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968526421/5000000000 : ℝ)^5399 ≤ (412232149361/3125000000000 : ℝ)^4375 := by
    have hnat : (968526421 : ℕ)^5399*3125000000000^4375 ≤ 412232149361^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968526421 5000000000 412232149361 3125000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171275319/1000000000 : ℝ), (3980644221/5000000000 : ℝ), (-968526421/5000000000 : ℝ)] ![(1133275698151/10000000000000 : ℝ), (75475814224163/100000000000000 : ℝ), (412232149361/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171275319/1000000000 : ℝ)|^5399 ≤ (1133275698151/10000000000000 : ℝ)^4375
        have hw : |(171275319/1000000000 : ℝ)|=(171275319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3980644221/5000000000 : ℝ)|^5399 ≤ (75475814224163/100000000000000 : ℝ)^4375
        have hw : |(3980644221/5000000000 : ℝ)|=(3980644221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-968526421/5000000000 : ℝ)|^5399 ≤ (412232149361/3125000000000 : ℝ)^4375
        have hw : |(-968526421/5000000000 : ℝ)|=(968526421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s4_9 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (819678683/5000000000 : ℝ)*x 0 + (325047817/625000000 : ℝ)*x 1 + (5201409647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819678683/5000000000 : ℝ)^5399 ≤ (2684122917767/25000000000000 : ℝ)^4375 := by
    have hnat : (819678683 : ℕ)^5399*25000000000000^4375 ≤ 2684122917767^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819678683 5000000000 2684122917767 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325047817/625000000 : ℝ)^5399 ≤ (22314170608437/50000000000000 : ℝ)^4375 := by
    have hnat : (325047817 : ℕ)^5399*50000000000000^4375 ≤ 22314170608437^4375*625000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325047817 625000000 22314170608437 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5201409647/10000000000 : ℝ)^5399 ≤ (1115879177377/2500000000000 : ℝ)^4375 := by
    have hnat : (5201409647 : ℕ)^5399*2500000000000^4375 ≤ 1115879177377^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201409647 10000000000 1115879177377 2500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819678683/5000000000 : ℝ), (325047817/625000000 : ℝ), (5201409647/10000000000 : ℝ)] ![(2684122917767/25000000000000 : ℝ), (22314170608437/50000000000000 : ℝ), (1115879177377/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819678683/5000000000 : ℝ)|^5399 ≤ (2684122917767/25000000000000 : ℝ)^4375
        have hw : |(819678683/5000000000 : ℝ)|=(819678683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325047817/625000000 : ℝ)|^5399 ≤ (22314170608437/50000000000000 : ℝ)^4375
        have hw : |(325047817/625000000 : ℝ)|=(325047817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5201409647/10000000000 : ℝ)|^5399 ≤ (1115879177377/2500000000000 : ℝ)^4375
        have hw : |(5201409647/10000000000 : ℝ)|=(5201409647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1722_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8503/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10101/100000 : ℝ) ^ (5391/1024 : ℝ) ≤ (114645876167423/20000000000000000000 : ℝ) := by
    have hpowers : (10101/100000 : ℝ)^5391 ≤ (114645876167423/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10101 : ℕ)^5391*20000000000000000000^1024 ≤ 114645876167423^1024*100000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10101 100000 114645876167423 20000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10101/100000 : ℝ)) (X := (114645876167423/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17007/100000 : ℝ) ^ (5391/1024 : ℝ) ≤ (4451387366952279/50000000000000000000 : ℝ) := by
    have hpowers : (17007/100000 : ℝ)^5391 ≤ (4451387366952279/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17007 : ℕ)^5391*50000000000000000000^1024 ≤ 4451387366952279^1024*100000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17007 100000 4451387366952279 50000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17007/100000 : ℝ)) (X := (4451387366952279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000114645876167423/10000000000000000000 : ℝ) ≤ (1250002722056021/1250000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (10000114645876167423/10000000000000000000 : ℝ)^1024 ≤ (1250002722056021/1250000000000000 : ℝ)^5391 := by
      have hnat : (10000114645876167423 : ℕ)^1024*1250000000000000^5391 ≤ 1250002722056021^5391*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000114645876167423 10000000000000000000 1250002722056021 1250000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002722056021/1250000000000000 : ℝ)) (X := (10000114645876167423/10000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100009476004114741673/100000000000000000000 : ℝ) ≤ (2000035997239153/2000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (100009476004114741673/100000000000000000000 : ℝ)^1024 ≤ (2000035997239153/2000000000000000 : ℝ)^5391 := by
      have hnat : (100009476004114741673 : ℕ)^1024*2000000000000000^5391 ≤ 2000035997239153^5391*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009476004114741673 100000000000000000000 2000035997239153 2000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000035997239153/2000000000000000 : ℝ)) (X := (100009476004114741673/100000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004451387366952279/25000000000000000000 : ℝ) ≤ (5000169097971681/5000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (25004451387366952279/25000000000000000000 : ℝ)^1024 ≤ (5000169097971681/5000000000000000 : ℝ)^5391 := by
      have hnat : (25004451387366952279 : ℕ)^1024*5000000000000000^5391 ≤ 5000169097971681^5391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004451387366952279 25000000000000000000 5000169097971681 5000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000169097971681/5000000000000000 : ℝ)) (X := (25004451387366952279/25000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(114645876167423/20000000000000000000 : ℝ) ≤ ((11509492372471682269/11510000000000000000 : ℝ)+2*(158209747597/690600000000000 : ℝ)*(10101/100000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (11509492372471682269/11510000000000000000 : ℝ)+2*(158209747597/690600000000000 : ℝ)*(10101/100000 : ℝ)=(1250002722056021/1250000000000000 : ℝ) by norm_num, show 1+2*(114645876167423/20000000000000000000 : ℝ)=(10000114645876167423/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4451387366952279/50000000000000000000 : ℝ)+(114645876167423/20000000000000000000 : ℝ) ≤ ((11509492372471682269/11510000000000000000 : ℝ)+(158209747597/690600000000000 : ℝ)*((17007/100000 : ℝ)+(10101/100000 : ℝ)))^(5391/1024 : ℝ) := by
    rw [show (11509492372471682269/11510000000000000000 : ℝ)+(158209747597/690600000000000 : ℝ)*((17007/100000 : ℝ)+(10101/100000 : ℝ))=(2000035997239153/2000000000000000 : ℝ) by norm_num, show 1+(4451387366952279/50000000000000000000 : ℝ)+(114645876167423/20000000000000000000 : ℝ)=(100009476004114741673/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4451387366952279/50000000000000000000 : ℝ) ≤ ((11509492372471682269/11510000000000000000 : ℝ)+2*(158209747597/690600000000000 : ℝ)*(17007/100000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (11509492372471682269/11510000000000000000 : ℝ)+2*(158209747597/690600000000000 : ℝ)*(17007/100000 : ℝ)=(5000169097971681/5000000000000000 : ℝ) by norm_num, show 1+2*(4451387366952279/50000000000000000000 : ℝ)=(25004451387366952279/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11509492372471682269/11510000000000000000 : ℝ)*(X 1 0+X 2 0)+(158209747597/690600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (10101/100000 : ℝ)) (hi := (17007/100000 : ℝ)) (c := (11509492372471682269/11510000000000000000 : ℝ)) (alpha := (158209747597/690600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11509492372471682269/11510000000000000000 : ℝ)*(X 0 1+X 2 1)+(158209747597/690600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (10101/100000 : ℝ)) (hi := (17007/100000 : ℝ)) (c := (11509492372471682269/11510000000000000000 : ℝ)) (alpha := (158209747597/690600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11509492372471682269/11510000000000000000 : ℝ)*(X 0 2+X 1 2)+(158209747597/690600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (10101/100000 : ℝ)) (hi := (17007/100000 : ℝ)) (c := (11509492372471682269/11510000000000000000 : ℝ)) (alpha := (158209747597/690600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1334869961/2500000000 : ℝ)*X 1 0+(-1537105029/10000000000 : ℝ)*X 1 1+(5139641731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4089600317/10000000000 : ℝ)*X 0 0+(906533941/2500000000 : ℝ)*X 0 1+(1146931157/2500000000 : ℝ)*X 0 2+(4089600317/10000000000 : ℝ)*X 1 0+(906533941/2500000000 : ℝ)*X 1 1+(1146931157/2500000000 : ℝ)*X 1 2+(4089600317/10000000000 : ℝ)*X 2 0+(906533941/2500000000 : ℝ)*X 2 1+(1146931157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1370022409/10000000000 : ℝ)*X 0 0+(2571627233/5000000000 : ℝ)*X 0 1+(6823493/12500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2626533313/5000000000 : ℝ)*X 1 0+(-608975617/5000000000 : ℝ)*X 1 1+(545879473/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1050613409/2000000000 : ℝ)*X 2 0+(5458792329/10000000000 : ℝ)*X 2 1+(-1217954057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2045014917/5000000000 : ℝ)*X 0 0+(915393019/2000000000 : ℝ)*X 0 1+(909263877/2500000000 : ℝ)*X 0 2+(2045014917/5000000000 : ℝ)*X 1 0+(915393019/2000000000 : ℝ)*X 1 1+(909263877/2500000000 : ℝ)*X 1 2+(2045014917/5000000000 : ℝ)*X 2 0+(915393019/2000000000 : ℝ)*X 2 1+(909263877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-22805261/5000000000 : ℝ)*X 0 0+(1424059127/2500000000 : ℝ)*X 0 1+(1424202793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1364329683/10000000000 : ℝ)*X 1 0+(-3088159583/10000000000 : ℝ)*X 1 1+(1462934263/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_7 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((171275319/1000000000 : ℝ)*X 2 0+(3980644221/5000000000 : ℝ)*X 2 1+(-968526421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_8 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((819678683/5000000000 : ℝ)*X 0 0+(325047817/625000000 : ℝ)*X 0 1+(5201409647/10000000000 : ℝ)*X 0 2+(819678683/5000000000 : ℝ)*X 1 0+(325047817/625000000 : ℝ)*X 1 1+(5201409647/10000000000 : ℝ)*X 1 2+(819678683/5000000000 : ℝ)*X 2 0+(325047817/625000000 : ℝ)*X 2 1+(5201409647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s4_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92454935386351629108923461/57550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (495944313/100000000000000 : ℝ)*(upper1) + (211656539523277/10000000000000 : ℝ)*(major0) + (211656539523277/10000000000000 : ℝ)*(major1) + (211656539523277/10000000000000 : ℝ)*(major2) + (23094228351/100000000000000 : ℝ)*(sp0) + (2158729993/100000000000000 : ℝ)*(sp1) + (1584592926906843/50000000000000 : ℝ)*(sp2) + (396145554122839/12500000000000 : ℝ)*(sp3) + (316918760854393/10000000000000 : ℝ)*(sp4) + (265984831622377/25000000000000 : ℝ)*(sp5) + (2763487813/100000000000000 : ℝ)*(sp6) + (272522609/25000000000000 : ℝ)*(sp7) + (1008757569/100000000000000 : ℝ)*(sp8) + (317197017/50000000000000 : ℝ)*(sp9) + (212788423922707/20000000000000 : ℝ)*(f.failure) + (6338377234603/200000000000 : ℝ)*(f.sum) + (225250106273/863250000000000000000000000 : ℝ)*base66 + (779388484777476539/345300000000000000000000000000000 : ℝ)*base67 + (1171990509671123461/345300000000000000000000000000000 : ℝ)*base70 + (617542714252176539/345300000000000000000000000000000 : ℝ)*base71 + (2505262076759/863250000000000000000000000 : ℝ)*base74 + (2169997786629623461/345300000000000000000000000000000 : ℝ)*base76 + (2886183321767376539/345300000000000000000000000000000 : ℝ)*base77 + (320784578381076539/345300000000000000000000000000000 : ℝ)*base79 + (2752030825081/690600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12853687/2000000000000000000000 : ℝ)*base89 + (12853687/2000000000000000000000 : ℝ)*base91 + (12853687/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1722_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8503/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1722_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1722_box_0 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060273741/10000000000 : ℝ)*x 0 + (5410965293/10000000000 : ℝ)*x 1 + (2705482387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060273741/10000000000 : ℝ)^5399 ≤ (3135307439543/50000000000000 : ℝ)^4375 := by
    have hnat : (1060273741 : ℕ)^5399*50000000000000^4375 ≤ 3135307439543^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060273741 10000000000 3135307439543 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410965293/10000000000 : ℝ)^5399 ≤ (23432347662263/50000000000000 : ℝ)^4375 := by
    have hnat : (5410965293 : ℕ)^5399*50000000000000^4375 ≤ 23432347662263^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410965293 10000000000 23432347662263 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705482387/5000000000 : ℝ)^5399 ≤ (2929043111083/6250000000000 : ℝ)^4375 := by
    have hnat : (2705482387 : ℕ)^5399*6250000000000^4375 ≤ 2929043111083^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705482387 5000000000 2929043111083 6250000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060273741/10000000000 : ℝ), (5410965293/10000000000 : ℝ), (2705482387/5000000000 : ℝ)] ![(3135307439543/50000000000000 : ℝ), (23432347662263/50000000000000 : ℝ), (2929043111083/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060273741/10000000000 : ℝ)|^5399 ≤ (3135307439543/50000000000000 : ℝ)^4375
        have hw : |(-1060273741/10000000000 : ℝ)|=(1060273741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410965293/10000000000 : ℝ)|^5399 ≤ (23432347662263/50000000000000 : ℝ)^4375
        have hw : |(5410965293/10000000000 : ℝ)|=(5410965293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705482387/5000000000 : ℝ)|^5399 ≤ (2929043111083/6250000000000 : ℝ)^4375
        have hw : |(2705482387/5000000000 : ℝ)|=(2705482387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_1 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224726599/10000000000 : ℝ)*x 0 + (-1324634529/10000000000 : ℝ)*x 1 + (2705482551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224726599/10000000000 : ℝ)^5399 ≤ (4488222040311/10000000000000 : ℝ)^4375 := by
    have hnat : (5224726599 : ℕ)^5399*10000000000000^4375 ≤ 4488222040311^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224726599 10000000000 4488222040311 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324634529/10000000000 : ℝ)^5399 ≤ (165061725967/2000000000000 : ℝ)^4375 := by
    have hnat : (1324634529 : ℕ)^5399*2000000000000^4375 ≤ 165061725967^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324634529 10000000000 165061725967 2000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705482551/5000000000 : ℝ)^5399 ≤ (183065208137/390625000000 : ℝ)^4375 := by
    have hnat : (2705482551 : ℕ)^5399*390625000000^4375 ≤ 183065208137^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705482551 5000000000 183065208137 390625000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224726599/10000000000 : ℝ), (-1324634529/10000000000 : ℝ), (2705482551/5000000000 : ℝ)] ![(4488222040311/10000000000000 : ℝ), (165061725967/2000000000000 : ℝ), (183065208137/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224726599/10000000000 : ℝ)|^5399 ≤ (4488222040311/10000000000000 : ℝ)^4375
        have hw : |(5224726599/10000000000 : ℝ)|=(5224726599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324634529/10000000000 : ℝ)|^5399 ≤ (165061725967/2000000000000 : ℝ)^4375
        have hw : |(-1324634529/10000000000 : ℝ)|=(1324634529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705482551/5000000000 : ℝ)|^5399 ≤ (183065208137/390625000000 : ℝ)^4375
        have hw : |(2705482551/5000000000 : ℝ)|=(2705482551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_2 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044945289/2000000000 : ℝ)*x 0 + (3381853/6250000 : ℝ)*x 1 + (-662317581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044945289/2000000000 : ℝ)^5399 ≤ (44882218770559/100000000000000 : ℝ)^4375 := by
    have hnat : (1044945289 : ℕ)^5399*100000000000000^4375 ≤ 44882218770559^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044945289 2000000000 44882218770559 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3381853/6250000 : ℝ)^5399 ≤ (23432345027611/50000000000000 : ℝ)^4375 := by
    have hnat : (3381853 : ℕ)^5399*50000000000000^4375 ≤ 23432345027611^4375*6250000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3381853 6250000 23432345027611 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662317581/5000000000 : ℝ)^5399 ≤ (8253091165327/100000000000000 : ℝ)^4375 := by
    have hnat : (662317581 : ℕ)^5399*100000000000000^4375 ≤ 8253091165327^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662317581 5000000000 8253091165327 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044945289/2000000000 : ℝ), (3381853/6250000 : ℝ), (-662317581/5000000000 : ℝ)] ![(44882218770559/100000000000000 : ℝ), (23432345027611/50000000000000 : ℝ), (8253091165327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044945289/2000000000 : ℝ)|^5399 ≤ (44882218770559/100000000000000 : ℝ)^4375
        have hw : |(1044945289/2000000000 : ℝ)|=(1044945289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3381853/6250000 : ℝ)|^5399 ≤ (23432345027611/50000000000000 : ℝ)^4375
        have hw : |(3381853/6250000 : ℝ)|=(3381853/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-662317581/5000000000 : ℝ)|^5399 ≤ (8253091165327/100000000000000 : ℝ)^4375
        have hw : |(-662317581/5000000000 : ℝ)|=(662317581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_3 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (139695711/312500000 : ℝ)*x 0 + (784071523/2000000000 : ℝ)*x 1 + (784071267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139695711/312500000 : ℝ)^5399 ≤ (37024653570621/100000000000000 : ℝ)^4375 := by
    have hnat : (139695711 : ℕ)^5399*100000000000000^4375 ≤ 37024653570621^4375*312500000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139695711 312500000 37024653570621 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (784071523/2000000000 : ℝ)^5399 ≤ (3935959943789/12500000000000 : ℝ)^4375 := by
    have hnat : (784071523 : ℕ)^5399*12500000000000^4375 ≤ 3935959943789^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784071523 2000000000 3935959943789 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (784071267/2000000000 : ℝ)^5399 ≤ (7871916715819/25000000000000 : ℝ)^4375 := by
    have hnat : (784071267 : ℕ)^5399*25000000000000^4375 ≤ 7871916715819^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784071267 2000000000 7871916715819 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139695711/312500000 : ℝ), (784071523/2000000000 : ℝ), (784071267/2000000000 : ℝ)] ![(37024653570621/100000000000000 : ℝ), (3935959943789/12500000000000 : ℝ), (7871916715819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139695711/312500000 : ℝ)|^5399 ≤ (37024653570621/100000000000000 : ℝ)^4375
        have hw : |(139695711/312500000 : ℝ)|=(139695711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(784071523/2000000000 : ℝ)|^5399 ≤ (3935959943789/12500000000000 : ℝ)^4375
        have hw : |(784071523/2000000000 : ℝ)|=(784071523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(784071267/2000000000 : ℝ)|^5399 ≤ (7871916715819/25000000000000 : ℝ)^4375
        have hw : |(784071267/2000000000 : ℝ)|=(784071267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_4 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-169991947/1000000000 : ℝ)*x 0 + (5177865703/10000000000 : ℝ)*x 1 + (5177865691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169991947/1000000000 : ℝ)^5399 ≤ (11228056931387/100000000000000 : ℝ)^4375 := by
    have hnat : (169991947 : ℕ)^5399*100000000000000^4375 ≤ 11228056931387^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169991947 1000000000 11228056931387 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177865703/10000000000 : ℝ)^5399 ≤ (22192985793843/50000000000000 : ℝ)^4375 := by
    have hnat : (5177865703 : ℕ)^5399*50000000000000^4375 ≤ 22192985793843^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177865703 10000000000 22192985793843 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177865691/10000000000 : ℝ)^5399 ≤ (22192985730371/50000000000000 : ℝ)^4375 := by
    have hnat : (5177865691 : ℕ)^5399*50000000000000^4375 ≤ 22192985730371^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177865691 10000000000 22192985730371 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169991947/1000000000 : ℝ), (5177865703/10000000000 : ℝ), (5177865691/10000000000 : ℝ)] ![(11228056931387/100000000000000 : ℝ), (22192985793843/50000000000000 : ℝ), (22192985730371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169991947/1000000000 : ℝ)|^5399 ≤ (11228056931387/100000000000000 : ℝ)^4375
        have hw : |(-169991947/1000000000 : ℝ)|=(169991947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177865703/10000000000 : ℝ)|^5399 ≤ (22192985793843/50000000000000 : ℝ)^4375
        have hw : |(5177865703/10000000000 : ℝ)|=(5177865703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177865691/10000000000 : ℝ)|^5399 ≤ (22192985730371/50000000000000 : ℝ)^4375
        have hw : |(5177865691/10000000000 : ℝ)|=(5177865691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_5 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382361863/10000000000 : ℝ)*x 0 + (-142798839/1000000000 : ℝ)*x 1 + (2588932839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382361863/10000000000 : ℝ)^5399 ≤ (46559164299083/100000000000000 : ℝ)^4375 := by
    have hnat : (5382361863 : ℕ)^5399*100000000000000^4375 ≤ 46559164299083^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382361863 10000000000 46559164299083 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142798839/1000000000 : ℝ)^5399 ≤ (4527432183123/50000000000000 : ℝ)^4375 := by
    have hnat : (142798839 : ℕ)^5399*50000000000000^4375 ≤ 4527432183123^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142798839 1000000000 4527432183123 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588932839/5000000000 : ℝ)^5399 ≤ (44385971323219/100000000000000 : ℝ)^4375 := by
    have hnat : (2588932839 : ℕ)^5399*100000000000000^4375 ≤ 44385971323219^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588932839 5000000000 44385971323219 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382361863/10000000000 : ℝ), (-142798839/1000000000 : ℝ), (2588932839/5000000000 : ℝ)] ![(46559164299083/100000000000000 : ℝ), (4527432183123/50000000000000 : ℝ), (44385971323219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382361863/10000000000 : ℝ)|^5399 ≤ (46559164299083/100000000000000 : ℝ)^4375
        have hw : |(5382361863/10000000000 : ℝ)|=(5382361863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142798839/1000000000 : ℝ)|^5399 ≤ (4527432183123/50000000000000 : ℝ)^4375
        have hw : |(-142798839/1000000000 : ℝ)|=(142798839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588932839/5000000000 : ℝ)|^5399 ≤ (44385971323219/100000000000000 : ℝ)^4375
        have hw : |(2588932839/5000000000 : ℝ)|=(2588932839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_6 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269118067/500000000 : ℝ)*x 0 + (5177866213/10000000000 : ℝ)*x 1 + (-71399419/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269118067/500000000 : ℝ)^5399 ≤ (23279579358031/50000000000000 : ℝ)^4375 := by
    have hnat : (269118067 : ℕ)^5399*50000000000000^4375 ≤ 23279579358031^4375*500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269118067 500000000 23279579358031 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177866213/10000000000 : ℝ)^5399 ≤ (44385976982797/100000000000000 : ℝ)^4375 := by
    have hnat : (5177866213 : ℕ)^5399*100000000000000^4375 ≤ 44385976982797^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177866213 10000000000 44385976982797 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71399419/500000000 : ℝ)^5399 ≤ (1810972857599/20000000000000 : ℝ)^4375 := by
    have hnat : (71399419 : ℕ)^5399*20000000000000^4375 ≤ 1810972857599^4375*500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71399419 500000000 1810972857599 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269118067/500000000 : ℝ), (5177866213/10000000000 : ℝ), (-71399419/500000000 : ℝ)] ![(23279579358031/50000000000000 : ℝ), (44385976982797/100000000000000 : ℝ), (1810972857599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269118067/500000000 : ℝ)|^5399 ≤ (23279579358031/50000000000000 : ℝ)^4375
        have hw : |(269118067/500000000 : ℝ)|=(269118067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177866213/10000000000 : ℝ)|^5399 ≤ (44385976982797/100000000000000 : ℝ)^4375
        have hw : |(5177866213/10000000000 : ℝ)|=(5177866213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71399419/500000000 : ℝ)|^5399 ≤ (1810972857599/20000000000000 : ℝ)^4375
        have hw : |(-71399419/500000000 : ℝ)|=(71399419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_7 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (115395939/312500000 : ℝ)*x 0 + (2154172099/5000000000 : ℝ)*x 1 + (4308344001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115395939/312500000 : ℝ)^5399 ≤ (29246470221401/100000000000000 : ℝ)^4375 := by
    have hnat : (115395939 : ℕ)^5399*100000000000000^4375 ≤ 29246470221401^4375*312500000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115395939 312500000 29246470221401 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154172099/5000000000 : ℝ)^5399 ≤ (8844191469883/25000000000000 : ℝ)^4375 := by
    have hnat : (2154172099 : ℕ)^5399*25000000000000^4375 ≤ 8844191469883^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154172099 5000000000 8844191469883 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4308344001/10000000000 : ℝ)^5399 ≤ (8844190970827/25000000000000 : ℝ)^4375 := by
    have hnat : (4308344001 : ℕ)^5399*25000000000000^4375 ≤ 8844190970827^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308344001 10000000000 8844190970827 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(115395939/312500000 : ℝ), (2154172099/5000000000 : ℝ), (4308344001/10000000000 : ℝ)] ![(29246470221401/100000000000000 : ℝ), (8844191469883/25000000000000 : ℝ), (8844190970827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(115395939/312500000 : ℝ)|^5399 ≤ (29246470221401/100000000000000 : ℝ)^4375
        have hw : |(115395939/312500000 : ℝ)|=(115395939/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2154172099/5000000000 : ℝ)|^5399 ≤ (8844191469883/25000000000000 : ℝ)^4375
        have hw : |(2154172099/5000000000 : ℝ)|=(2154172099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4308344001/10000000000 : ℝ)|^5399 ≤ (8844190970827/25000000000000 : ℝ)^4375
        have hw : |(4308344001/10000000000 : ℝ)|=(4308344001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_8 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12204607/78125000 : ℝ)*x 0 + (200209629/400000000 : ℝ)*x 1 + (272660777/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12204607/78125000 : ℝ)^5399 ≤ (10116292979023/100000000000000 : ℝ)^4375 := by
    have hnat : (12204607 : ℕ)^5399*100000000000000^4375 ≤ 10116292979023^4375*78125000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12204607 78125000 10116292979023 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200209629/400000000 : ℝ)^5399 ≤ (42567018942249/100000000000000 : ℝ)^4375 := by
    have hnat : (200209629 : ℕ)^5399*100000000000000^4375 ≤ 42567018942249^4375*400000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200209629 400000000 42567018942249 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272660777/500000000 : ℝ)^5399 ≤ (47316688062333/100000000000000 : ℝ)^4375 := by
    have hnat : (272660777 : ℕ)^5399*100000000000000^4375 ≤ 47316688062333^4375*500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272660777 500000000 47316688062333 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12204607/78125000 : ℝ), (200209629/400000000 : ℝ), (272660777/500000000 : ℝ)] ![(10116292979023/100000000000000 : ℝ), (42567018942249/100000000000000 : ℝ), (47316688062333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12204607/78125000 : ℝ)|^5399 ≤ (10116292979023/100000000000000 : ℝ)^4375
        have hw : |(-12204607/78125000 : ℝ)|=(12204607/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200209629/400000000 : ℝ)|^5399 ≤ (42567018942249/100000000000000 : ℝ)^4375
        have hw : |(200209629/400000000 : ℝ)|=(200209629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272660777/500000000 : ℝ)|^5399 ≤ (47316688062333/100000000000000 : ℝ)^4375
        have hw : |(272660777/500000000 : ℝ)|=(272660777/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_9 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598088959/5000000000 : ℝ)*x 0 + (-130515137/1000000000 : ℝ)*x 1 + (1363303831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598088959/5000000000 : ℝ)^5399 ≤ (22289885096499/50000000000000 : ℝ)^4375 := by
    have hnat : (2598088959 : ℕ)^5399*50000000000000^4375 ≤ 22289885096499^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598088959 5000000000 22289885096499 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130515137/1000000000 : ℝ)^5399 ≤ (810354403953/10000000000000 : ℝ)^4375 := by
    have hnat : (130515137 : ℕ)^5399*10000000000000^4375 ≤ 810354403953^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130515137 1000000000 810354403953 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363303831/2500000000 : ℝ)^5399 ≤ (23658342874733/50000000000000 : ℝ)^4375 := by
    have hnat : (1363303831 : ℕ)^5399*50000000000000^4375 ≤ 23658342874733^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363303831 2500000000 23658342874733 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598088959/5000000000 : ℝ), (-130515137/1000000000 : ℝ), (1363303831/2500000000 : ℝ)] ![(22289885096499/50000000000000 : ℝ), (810354403953/10000000000000 : ℝ), (23658342874733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598088959/5000000000 : ℝ)|^5399 ≤ (22289885096499/50000000000000 : ℝ)^4375
        have hw : |(2598088959/5000000000 : ℝ)|=(2598088959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130515137/1000000000 : ℝ)|^5399 ≤ (810354403953/10000000000000 : ℝ)^4375
        have hw : |(-130515137/1000000000 : ℝ)|=(130515137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363303831/2500000000 : ℝ)|^5399 ≤ (23658342874733/50000000000000 : ℝ)^4375
        have hw : |(1363303831/2500000000 : ℝ)|=(1363303831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_10 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196177517/10000000000 : ℝ)*x 0 + (1363303873/2500000000 : ℝ)*x 1 + (-130515169/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196177517/10000000000 : ℝ)^5399 ≤ (44579765947453/100000000000000 : ℝ)^4375 := by
    have hnat : (5196177517 : ℕ)^5399*100000000000000^4375 ≤ 44579765947453^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196177517 10000000000 44579765947453 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363303873/2500000000 : ℝ)^5399 ≤ (23658343774181/50000000000000 : ℝ)^4375 := by
    have hnat : (1363303873 : ℕ)^5399*50000000000000^4375 ≤ 23658343774181^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363303873 2500000000 23658343774181 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130515169/1000000000 : ℝ)^5399 ≤ (810354649141/10000000000000 : ℝ)^4375 := by
    have hnat : (130515169 : ℕ)^5399*10000000000000^4375 ≤ 810354649141^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130515169 1000000000 810354649141 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196177517/10000000000 : ℝ), (1363303873/2500000000 : ℝ), (-130515169/1000000000 : ℝ)] ![(44579765947453/100000000000000 : ℝ), (23658343774181/50000000000000 : ℝ), (810354649141/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196177517/10000000000 : ℝ)|^5399 ≤ (44579765947453/100000000000000 : ℝ)^4375
        have hw : |(5196177517/10000000000 : ℝ)|=(5196177517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363303873/2500000000 : ℝ)|^5399 ≤ (23658343774181/50000000000000 : ℝ)^4375
        have hw : |(1363303873/2500000000 : ℝ)|=(1363303873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130515169/1000000000 : ℝ)|^5399 ≤ (810354649141/10000000000000 : ℝ)^4375
        have hw : |(-130515169/1000000000 : ℝ)|=(130515169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_11 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4606245659/10000000000 : ℝ)*x 0 + (3849847203/10000000000 : ℝ)*x 1 + (3849847579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4606245659/10000000000 : ℝ)^5399 ≤ (38419444311537/100000000000000 : ℝ)^4375 := by
    have hnat : (4606245659 : ℕ)^5399*100000000000000^4375 ≤ 38419444311537^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606245659 10000000000 38419444311537 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3849847203/10000000000 : ℝ)^5399 ≤ (30790275975219/100000000000000 : ℝ)^4375 := by
    have hnat : (3849847203 : ℕ)^5399*100000000000000^4375 ≤ 30790275975219^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3849847203 10000000000 30790275975219 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3849847579/10000000000 : ℝ)^5399 ≤ (30790279686239/100000000000000 : ℝ)^4375 := by
    have hnat : (3849847579 : ℕ)^5399*100000000000000^4375 ≤ 30790279686239^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3849847579 10000000000 30790279686239 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4606245659/10000000000 : ℝ), (3849847203/10000000000 : ℝ), (3849847579/10000000000 : ℝ)] ![(38419444311537/100000000000000 : ℝ), (30790275975219/100000000000000 : ℝ), (30790279686239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4606245659/10000000000 : ℝ)|^5399 ≤ (38419444311537/100000000000000 : ℝ)^4375
        have hw : |(4606245659/10000000000 : ℝ)|=(4606245659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3849847203/10000000000 : ℝ)|^5399 ≤ (30790275975219/100000000000000 : ℝ)^4375
        have hw : |(3849847203/10000000000 : ℝ)|=(3849847203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3849847579/10000000000 : ℝ)|^5399 ≤ (30790279686239/100000000000000 : ℝ)^4375
        have hw : |(3849847579/10000000000 : ℝ)|=(3849847579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_12 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-298055751/2500000000 : ℝ)*x 0 + (5575636763/10000000000 : ℝ)*x 1 + (5152879439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (298055751/2500000000 : ℝ)^5399 ≤ (7247235468191/100000000000000 : ℝ)^4375 := by
    have hnat : (298055751 : ℕ)^5399*100000000000000^4375 ≤ 7247235468191^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298055751 2500000000 7247235468191 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5575636763/10000000000 : ℝ)^5399 ≤ (4863096440247/10000000000000 : ℝ)^4375 := by
    have hnat : (5575636763 : ℕ)^5399*10000000000000^4375 ≤ 4863096440247^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575636763 10000000000 4863096440247 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152879439/10000000000 : ℝ)^5399 ≤ (2757612507429/6250000000000 : ℝ)^4375 := by
    have hnat : (5152879439 : ℕ)^5399*6250000000000^4375 ≤ 2757612507429^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152879439 10000000000 2757612507429 6250000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-298055751/2500000000 : ℝ), (5575636763/10000000000 : ℝ), (5152879439/10000000000 : ℝ)] ![(7247235468191/100000000000000 : ℝ), (4863096440247/10000000000000 : ℝ), (2757612507429/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-298055751/2500000000 : ℝ)|^5399 ≤ (7247235468191/100000000000000 : ℝ)^4375
        have hw : |(-298055751/2500000000 : ℝ)|=(298055751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5575636763/10000000000 : ℝ)|^5399 ≤ (4863096440247/10000000000000 : ℝ)^4375
        have hw : |(5575636763/10000000000 : ℝ)|=(5575636763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152879439/10000000000 : ℝ)|^5399 ≤ (2757612507429/6250000000000 : ℝ)^4375
        have hw : |(5152879439/10000000000 : ℝ)|=(5152879439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_13 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349822811/2500000000 : ℝ)*x 0 + (-179829353/1250000000 : ℝ)*x 1 + (2576439779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349822811/2500000000 : ℝ)^5399 ≤ (46739951773239/100000000000000 : ℝ)^4375 := by
    have hnat : (1349822811 : ℕ)^5399*100000000000000^4375 ≤ 46739951773239^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349822811 2500000000 46739951773239 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179829353/1250000000 : ℝ)^5399 ≤ (228456170891/2500000000000 : ℝ)^4375 := by
    have hnat : (179829353 : ℕ)^5399*2500000000000^4375 ≤ 228456170891^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179829353 1250000000 228456170891 2500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576439779/5000000000 : ℝ)^5399 ≤ (44121801376299/100000000000000 : ℝ)^4375 := by
    have hnat : (2576439779 : ℕ)^5399*100000000000000^4375 ≤ 44121801376299^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576439779 5000000000 44121801376299 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349822811/2500000000 : ℝ), (-179829353/1250000000 : ℝ), (2576439779/5000000000 : ℝ)] ![(46739951773239/100000000000000 : ℝ), (228456170891/2500000000000 : ℝ), (44121801376299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349822811/2500000000 : ℝ)|^5399 ≤ (46739951773239/100000000000000 : ℝ)^4375
        have hw : |(1349822811/2500000000 : ℝ)|=(1349822811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179829353/1250000000 : ℝ)|^5399 ≤ (228456170891/2500000000000 : ℝ)^4375
        have hw : |(-179829353/1250000000 : ℝ)|=(179829353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576439779/5000000000 : ℝ)|^5399 ≤ (44121801376299/100000000000000 : ℝ)^4375
        have hw : |(2576439779/5000000000 : ℝ)|=(2576439779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_14 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674911421/1250000000 : ℝ)*x 0 + (5152879483/10000000000 : ℝ)*x 1 + (-1438634757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674911421/1250000000 : ℝ)^5399 ≤ (5842494137239/12500000000000 : ℝ)^4375 := by
    have hnat : (674911421 : ℕ)^5399*12500000000000^4375 ≤ 5842494137239^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674911421 1250000000 5842494137239 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152879483/10000000000 : ℝ)^5399 ≤ (22060900291899/50000000000000 : ℝ)^4375 := by
    have hnat : (5152879483 : ℕ)^5399*50000000000000^4375 ≤ 22060900291899^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152879483 10000000000 22060900291899 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1438634757/10000000000 : ℝ)^5399 ≤ (4569123155221/50000000000000 : ℝ)^4375 := by
    have hnat : (1438634757 : ℕ)^5399*50000000000000^4375 ≤ 4569123155221^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438634757 10000000000 4569123155221 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674911421/1250000000 : ℝ), (5152879483/10000000000 : ℝ), (-1438634757/10000000000 : ℝ)] ![(5842494137239/12500000000000 : ℝ), (22060900291899/50000000000000 : ℝ), (4569123155221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674911421/1250000000 : ℝ)|^5399 ≤ (5842494137239/12500000000000 : ℝ)^4375
        have hw : |(674911421/1250000000 : ℝ)|=(674911421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152879483/10000000000 : ℝ)|^5399 ≤ (22060900291899/50000000000000 : ℝ)^4375
        have hw : |(5152879483/10000000000 : ℝ)|=(5152879483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1438634757/10000000000 : ℝ)|^5399 ≤ (4569123155221/50000000000000 : ℝ)^4375
        have hw : |(-1438634757/10000000000 : ℝ)|=(1438634757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_box_15 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3606336353/10000000000 : ℝ)*x 0 + (2174909821/5000000000 : ℝ)*x 1 + (1087454843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3606336353/10000000000 : ℝ)^5399 ≤ (1420248768289/5000000000000 : ℝ)^4375 := by
    have hnat : (3606336353 : ℕ)^5399*5000000000000^4375 ≤ 1420248768289^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3606336353 10000000000 1420248768289 5000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174909821/5000000000 : ℝ)^5399 ≤ (17898756841317/50000000000000 : ℝ)^4375 := by
    have hnat : (2174909821 : ℕ)^5399*50000000000000^4375 ≤ 17898756841317^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174909821 5000000000 17898756841317 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087454843/2500000000 : ℝ)^5399 ≤ (35797510940551/100000000000000 : ℝ)^4375 := by
    have hnat : (1087454843 : ℕ)^5399*100000000000000^4375 ≤ 35797510940551^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087454843 2500000000 35797510940551 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3606336353/10000000000 : ℝ), (2174909821/5000000000 : ℝ), (1087454843/2500000000 : ℝ)] ![(1420248768289/5000000000000 : ℝ), (17898756841317/50000000000000 : ℝ), (35797510940551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3606336353/10000000000 : ℝ)|^5399 ≤ (1420248768289/5000000000000 : ℝ)^4375
        have hw : |(3606336353/10000000000 : ℝ)|=(3606336353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2174909821/5000000000 : ℝ)|^5399 ≤ (17898756841317/50000000000000 : ℝ)^4375
        have hw : |(2174909821/5000000000 : ℝ)|=(2174909821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087454843/2500000000 : ℝ)|^5399 ≤ (35797510940551/100000000000000 : ℝ)^4375
        have hw : |(1087454843/2500000000 : ℝ)|=(1087454843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1722_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8503/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(33431/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58683/100000 : ℝ) ∧ (40931/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90591/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8503/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8503/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8503/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8503/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8503/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8503/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10101/100000 : ℝ) ^ (5391/1024 : ℝ) ≤ (114645876167423/20000000000000000000 : ℝ) := by
    have hpowers : (10101/100000 : ℝ)^5391 ≤ (114645876167423/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10101 : ℕ)^5391*20000000000000000000^1024 ≤ 114645876167423^1024*100000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10101 100000 114645876167423 20000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10101/100000 : ℝ)) (X := (114645876167423/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8503/50000 : ℝ) ^ (5391/1024 : ℝ) ≤ (8900019156615951/100000000000000000000 : ℝ) := by
    have hpowers : (8503/50000 : ℝ)^5391 ≤ (8900019156615951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8503 : ℕ)^5391*100000000000000000000^1024 ≤ 8900019156615951^1024*50000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8503 50000 8900019156615951 100000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8503/50000 : ℝ)) (X := (8900019156615951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000114645876167423/10000000000000000000 : ℝ) ≤ (1250002722056021/1250000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (10000114645876167423/10000000000000000000 : ℝ)^1024 ≤ (1250002722056021/1250000000000000 : ℝ)^5391 := by
      have hnat : (10000114645876167423 : ℕ)^1024*1250000000000000^5391 ≤ 1250002722056021^5391*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000114645876167423 10000000000000000000 1250002722056021 1250000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002722056021/1250000000000000 : ℝ)) (X := (10000114645876167423/10000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004736624268726533/50000000000000000000 : ℝ) ≤ (10000179933858637/10000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (50004736624268726533/50000000000000000000 : ℝ)^1024 ≤ (10000179933858637/10000000000000000 : ℝ)^5391 := by
      have hnat : (50004736624268726533 : ℕ)^1024*10000000000000000^5391 ≤ 10000179933858637^5391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004736624268726533 50000000000000000000 10000179933858637 10000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000179933858637/10000000000000000 : ℝ)) (X := (50004736624268726533/50000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008900019156615951/50000000000000000000 : ℝ) ≤ (5000169045634553/5000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (50008900019156615951/50000000000000000000 : ℝ)^1024 ≤ (5000169045634553/5000000000000000 : ℝ)^5391 := by
      have hnat : (50008900019156615951 : ℕ)^1024*5000000000000000^5391 ≤ 5000169045634553^5391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008900019156615951 50000000000000000000 5000169045634553 5000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000169045634553/5000000000000000 : ℝ)) (X := (50008900019156615951/50000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(114645876167423/20000000000000000000 : ℝ) ≤ ((34523477635184152651/34525000000000000000 : ℝ)+2*(158157410469/690500000000000 : ℝ)*(10101/100000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (34523477635184152651/34525000000000000000 : ℝ)+2*(158157410469/690500000000000 : ℝ)*(10101/100000 : ℝ)=(1250002722056021/1250000000000000 : ℝ) by norm_num, show 1+2*(114645876167423/20000000000000000000 : ℝ)=(10000114645876167423/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8900019156615951/100000000000000000000 : ℝ)+(114645876167423/20000000000000000000 : ℝ) ≤ ((34523477635184152651/34525000000000000000 : ℝ)+(158157410469/690500000000000 : ℝ)*((8503/50000 : ℝ)+(10101/100000 : ℝ)))^(5391/1024 : ℝ) := by
    rw [show (34523477635184152651/34525000000000000000 : ℝ)+(158157410469/690500000000000 : ℝ)*((8503/50000 : ℝ)+(10101/100000 : ℝ))=(10000179933858637/10000000000000000 : ℝ) by norm_num, show 1+(8900019156615951/100000000000000000000 : ℝ)+(114645876167423/20000000000000000000 : ℝ)=(50004736624268726533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8900019156615951/100000000000000000000 : ℝ) ≤ ((34523477635184152651/34525000000000000000 : ℝ)+2*(158157410469/690500000000000 : ℝ)*(8503/50000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (34523477635184152651/34525000000000000000 : ℝ)+2*(158157410469/690500000000000 : ℝ)*(8503/50000 : ℝ)=(5000169045634553/5000000000000000 : ℝ) by norm_num, show 1+2*(8900019156615951/100000000000000000000 : ℝ)=(50008900019156615951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34523477635184152651/34525000000000000000 : ℝ)*(X 1 0+X 2 0)+(158157410469/690500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (10101/100000 : ℝ)) (hi := (8503/50000 : ℝ)) (c := (34523477635184152651/34525000000000000000 : ℝ)) (alpha := (158157410469/690500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34523477635184152651/34525000000000000000 : ℝ)*(X 0 1+X 2 1)+(158157410469/690500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (10101/100000 : ℝ)) (hi := (8503/50000 : ℝ)) (c := (34523477635184152651/34525000000000000000 : ℝ)) (alpha := (158157410469/690500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34523477635184152651/34525000000000000000 : ℝ)*(X 0 2+X 1 2)+(158157410469/690500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (10101/100000 : ℝ)) (hi := (8503/50000 : ℝ)) (c := (34523477635184152651/34525000000000000000 : ℝ)) (alpha := (158157410469/690500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1060273741/10000000000 : ℝ)*X 0 0+(5410965293/10000000000 : ℝ)*X 0 1+(2705482387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5224726599/10000000000 : ℝ)*X 1 0+(-1324634529/10000000000 : ℝ)*X 1 1+(2705482551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1044945289/2000000000 : ℝ)*X 2 0+(3381853/6250000 : ℝ)*X 2 1+(-662317581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((139695711/312500000 : ℝ)*X 0 0+(784071523/2000000000 : ℝ)*X 0 1+(784071267/2000000000 : ℝ)*X 0 2+(139695711/312500000 : ℝ)*X 1 0+(784071523/2000000000 : ℝ)*X 1 1+(784071267/2000000000 : ℝ)*X 1 2+(139695711/312500000 : ℝ)*X 2 0+(784071523/2000000000 : ℝ)*X 2 1+(784071267/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-169991947/1000000000 : ℝ)*X 0 0+(5177865703/10000000000 : ℝ)*X 0 1+(5177865691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5382361863/10000000000 : ℝ)*X 1 0+(-142798839/1000000000 : ℝ)*X 1 1+(2588932839/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((269118067/500000000 : ℝ)*X 2 0+(5177866213/10000000000 : ℝ)*X 2 1+(-71399419/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((115395939/312500000 : ℝ)*X 0 0+(2154172099/5000000000 : ℝ)*X 0 1+(4308344001/10000000000 : ℝ)*X 0 2+(115395939/312500000 : ℝ)*X 1 0+(2154172099/5000000000 : ℝ)*X 1 1+(4308344001/10000000000 : ℝ)*X 1 2+(115395939/312500000 : ℝ)*X 2 0+(2154172099/5000000000 : ℝ)*X 2 1+(4308344001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-12204607/78125000 : ℝ)*X 0 0+(200209629/400000000 : ℝ)*X 0 1+(272660777/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598088959/5000000000 : ℝ)*X 1 0+(-130515137/1000000000 : ℝ)*X 1 1+(1363303831/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196177517/10000000000 : ℝ)*X 2 0+(1363303873/2500000000 : ℝ)*X 2 1+(-130515169/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4606245659/10000000000 : ℝ)*X 0 0+(3849847203/10000000000 : ℝ)*X 0 1+(3849847579/10000000000 : ℝ)*X 0 2+(4606245659/10000000000 : ℝ)*X 1 0+(3849847203/10000000000 : ℝ)*X 1 1+(3849847579/10000000000 : ℝ)*X 1 2+(4606245659/10000000000 : ℝ)*X 2 0+(3849847203/10000000000 : ℝ)*X 2 1+(3849847579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-298055751/2500000000 : ℝ)*X 0 0+(5575636763/10000000000 : ℝ)*X 0 1+(5152879439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1349822811/2500000000 : ℝ)*X 1 0+(-179829353/1250000000 : ℝ)*X 1 1+(2576439779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((674911421/1250000000 : ℝ)*X 2 0+(5152879483/10000000000 : ℝ)*X 2 1+(-1438634757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3606336353/10000000000 : ℝ)*X 0 0+(2174909821/5000000000 : ℝ)*X 0 1+(1087454843/2500000000 : ℝ)*X 0 2+(3606336353/10000000000 : ℝ)*X 1 0+(2174909821/5000000000 : ℝ)*X 1 1+(1087454843/2500000000 : ℝ)*X 1 2+(3606336353/10000000000 : ℝ)*X 2 0+(2174909821/5000000000 : ℝ)*X 2 1+(1087454843/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33431/50000 : ℝ) ≤ (-36067755037428755012368889940429/53945312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3383711/50000000000000 : ℝ)*(lower0) + (30239489/100000000000000 : ℝ)*(upper1) + (140501/100000000000000 : ℝ)*(upper3) + (53819491/100000000000000 : ℝ)*(lower4) + (9674983/100000000000000 : ℝ)*(lower5) + (173364858840511/12500000000000 : ℝ)*(major0) + (173364858840511/12500000000000 : ℝ)*(major1) + (173364858840511/12500000000000 : ℝ)*(major2) + (524739120290439/25000000000000 : ℝ)*(sp4) + (1049472763471057/50000000000000 : ℝ)*(sp5) + (2098912476067131/100000000000000 : ℝ)*(sp6) + (34858393848207/5000000000000 : ℝ)*(sp7) + (10954219643/100000000000000 : ℝ)*(sp13) + (22002547313/50000000000000 : ℝ)*(sp14) + (34858393848207/5000000000000 : ℝ)*(f.failure) + (524739120290439/25000000000000 : ℝ)*(f.sum) + (2911055154027/539453125000000000000000000 : ℝ)*base66 + (1732033937111044661/431562500000000000000000000000000 : ℝ)*base67 + (4039976954739794661/431562500000000000000000000000000 : ℝ)*base69 + (1380251881978330339/431562500000000000000000000000000 : ℝ)*base72 + (42779702368607/8631250000000000000000000000 : ℝ)*base74 + (2134021011024169661/431562500000000000000000000000000 : ℝ)*base75 + (78774775973544661/431562500000000000000000000000000 : ℝ)*base77 + (641886004881982161/431562500000000000000000000000000 : ℝ)*base79 + (49238019212161/17262500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (349187/500000000000000000000 : ℝ)*base89 + (349187/500000000000000000000 : ℝ)*base91 + (349187/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58683/100000 : ℝ) ≤ (506525742002372120399002011237621/863125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10864417/100000000000000 : ℝ)*(lower0) + (2909121/10000000000000 : ℝ)*(upper1) + (33030949/50000000000000 : ℝ)*(upper2) + (108736893/100000000000000 : ℝ)*(upper3) + (66232133/100000000000000 : ℝ)*(lower5) + (747608101288157/50000000000000 : ℝ)*(major0) + (747608101288157/50000000000000 : ℝ)*(major1) + (747608101288157/50000000000000 : ℝ)*(major2) + (88770583610683/4000000000000 : ℝ)*(sp0) + (1109631484036761/50000000000000 : ℝ)*(sp1) + (2219251799464009/100000000000000 : ℝ)*(sp2) + (37580305797133/5000000000000 : ℝ)*(sp3) + (1622193553/100000000000000 : ℝ)*(sp9) + (6395401533/50000000000000 : ℝ)*(sp10) + (37580305797133/5000000000000 : ℝ)*(f.failure) + (88770583610683/4000000000000 : ℝ)*(f.sum) + (4442849760141/34525000000000000000000000000 : ℝ)*base65 + (2401950947189354207/1726250000000000000000000000000000 : ℝ)*base67 + (16177131056279395793/1726250000000000000000000000000000 : ℝ)*base70 + (5828275256606895793/1726250000000000000000000000000000 : ℝ)*base72 + (217778704179233/17262500000000000000000000000 : ℝ)*base73 + (4695530486836895793/1726250000000000000000000000000000 : ℝ)*base76 + (11991524266475645793/1726250000000000000000000000000000 : ℝ)*base78 + (6247080127743104207/1726250000000000000000000000000000 : ℝ)*base79 + (15628408903821/8631250000000000000000000000 : ℝ)*base82 + (2116247/500000000000000000000 : ℝ)*base90 + (2116247/500000000000000000000 : ℝ)*base92 + (2116247/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40931/50000 : ℝ) ≤ (176648941801365989969517458833443/215781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22426481/25000000000000 : ℝ)*(upper2) + (13638253/25000000000000 : ℝ)*(lower3) + (890237/12500000000000 : ℝ)*(lower4) + (23118241/25000000000000 : ℝ)*(lower5) + (377264981848581/25000000000000 : ℝ)*(major0) + (377264981848581/25000000000000 : ℝ)*(major1) + (377264981848581/25000000000000 : ℝ)*(major2) + (320239353/12500000000000 : ℝ)*(sp1) + (2669648819/50000000000000 : ℝ)*(sp3) + (162996039/100000000000000 : ℝ)*(sp4) + (558066605562539/25000000000000 : ℝ)*(sp8) + (2232264023331371/100000000000000 : ℝ)*(sp9) + (446453317049239/20000000000000 : ℝ)*(sp10) + (94819956922863/12500000000000 : ℝ)*(sp11) + (758564994680541/100000000000000 : ℝ)*(f.failure) + (446453317049239/20000000000000 : ℝ)*(f.sum) + (120345568584597/17262500000000000000000000000 : ℝ)*base66 + (1002701268409313231/863125000000000000000000000000000 : ℝ)*base67 + (3057493916350686769/863125000000000000000000000000000 : ℝ)*base70 + (564801285795061769/863125000000000000000000000000000 : ℝ)*base72 + (3437283119757/4315625000000000000000000000 : ℝ)*base73 + (5002959595102561769/863125000000000000000000000000000 : ℝ)*base76 + (9417640211320686769/863125000000000000000000000000000 : ℝ)*base78 + (892979671067561769/863125000000000000000000000000000 : ℝ)*base80 + (4117511653059/2157812500000000000000000000 : ℝ)*base82 + (45667719/10000000000000000000000 : ℝ)*base90 + (45667719/10000000000000000000000 : ℝ)*base92 + (45667719/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-90591/100000 : ℝ) ≤ (-39094707770752440642983261365719/43156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4837171/100000000000000 : ℝ)*(lower0) + (30323309/100000000000000 : ℝ)*(lower2) + (138207/12500000000000 : ℝ)*(upper3) + (38989969606373/2500000000000 : ℝ)*(major0) + (38989969606373/2500000000000 : ℝ)*(major1) + (38989969606373/2500000000000 : ℝ)*(major2) + (135049311/12500000000000 : ℝ)*(sp0) + (1572497317/50000000000000 : ℝ)*(sp5) + (511780971/20000000000000 : ℝ)*(sp6) + (46731757/20000000000000 : ℝ)*(sp8) + (118271147362567/5000000000000 : ℝ)*(sp12) + (118271055815499/5000000000000 : ℝ)*(sp13) + (1182710851199879/50000000000000 : ℝ)*(sp14) + (783969557474687/100000000000000 : ℝ)*(sp15) + (783969557474687/100000000000000 : ℝ)*(f.failure) + (1182712130652307/50000000000000 : ℝ)*(f.sum) + (3910561272119/6905000000000000000000000000 : ℝ)*base66 + (424857713766107323/86312500000000000000000000000000 : ℝ)*base67 + (57211272641544823/86312500000000000000000000000000 : ℝ)*base69 + (343523452383267677/86312500000000000000000000000000 : ℝ)*base72 + (7621239382263/3452500000000000000000000000 : ℝ)*base73 + (266778044197205177/86312500000000000000000000000000 : ℝ)*base76 + (126022038645357323/86312500000000000000000000000000 : ℝ)*base77 + (339322656347357323/86312500000000000000000000000000 : ℝ)*base79 + (7639168241497/3452500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (63037133/10000000000000000000000 : ℝ)*base90 + (63037133/10000000000000000000000 : ℝ)*base92 + (63037133/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1722_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8503/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58683/100000 : ℝ) else (40931/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90591/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1722_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1722_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58683/100000 : ℝ) else (40931/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90591/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1722_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1722_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1722_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58683/100000 : ℝ) else (40931/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90591/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1722_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

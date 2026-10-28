-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:03.96649+00:00
-- url     : https://prove2.me/submissions/5f416291-d4ec-4f08-8cdc-9fe2513f65e0

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
theorem support_rectangle_w1039_s9_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336257119/2500000000 : ℝ)*x 0 + (5263970827/10000000000 : ℝ)*x 1 + (-570879747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336257119/2500000000 : ℝ)^1029 ≤ (21718172061247/50000000000000 : ℝ)^773 := by
    have hnat : (1336257119 : ℕ)^1029*50000000000000^773 ≤ 21718172061247^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336257119 2500000000 21718172061247 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263970827/10000000000 : ℝ)^1029 ≤ (42561687776979/100000000000000 : ℝ)^773 := by
    have hnat : (5263970827 : ℕ)^1029*100000000000000^773 ≤ 42561687776979^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263970827 10000000000 42561687776979 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570879747/2500000000 : ℝ)^1029 ≤ (22403148931/160000000000 : ℝ)^773 := by
    have hnat : (570879747 : ℕ)^1029*160000000000^773 ≤ 22403148931^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570879747 2500000000 22403148931 160000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336257119/2500000000 : ℝ), (5263970827/10000000000 : ℝ), (-570879747/2500000000 : ℝ)] ![(21718172061247/50000000000000 : ℝ), (42561687776979/100000000000000 : ℝ), (22403148931/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336257119/2500000000 : ℝ)|^1029 ≤ (21718172061247/50000000000000 : ℝ)^773
        have hw : |(1336257119/2500000000 : ℝ)|=(1336257119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263970827/10000000000 : ℝ)|^1029 ≤ (42561687776979/100000000000000 : ℝ)^773
        have hw : |(5263970827/10000000000 : ℝ)|=(5263970827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-570879747/2500000000 : ℝ)|^1029 ≤ (22403148931/160000000000 : ℝ)^773
        have hw : |(-570879747/2500000000 : ℝ)|=(570879747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s9_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108569591/5000000000 : ℝ)*x 0 + (5264298157/10000000000 : ℝ)*x 1 + (1078894129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108569591/5000000000 : ℝ)^1029 ≤ (420711614183/3125000000000 : ℝ)^773 := by
    have hnat : (1108569591 : ℕ)^1029*3125000000000^773 ≤ 420711614183^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108569591 5000000000 420711614183 3125000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264298157/10000000000 : ℝ)^1029 ≤ (212826054651/500000000000 : ℝ)^773 := by
    have hnat : (5264298157 : ℕ)^1029*500000000000^773 ≤ 212826054651^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264298157 10000000000 212826054651 500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078894129/2000000000 : ℝ)^1029 ≤ (43972017397089/100000000000000 : ℝ)^773 := by
    have hnat : (1078894129 : ℕ)^1029*100000000000000^773 ≤ 43972017397089^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078894129 2000000000 43972017397089 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108569591/5000000000 : ℝ), (5264298157/10000000000 : ℝ), (1078894129/2000000000 : ℝ)] ![(420711614183/3125000000000 : ℝ), (212826054651/500000000000 : ℝ), (43972017397089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108569591/5000000000 : ℝ)|^1029 ≤ (420711614183/3125000000000 : ℝ)^773
        have hw : |(-1108569591/5000000000 : ℝ)|=(1108569591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264298157/10000000000 : ℝ)|^1029 ≤ (212826054651/500000000000 : ℝ)^773
        have hw : |(5264298157/10000000000 : ℝ)|=(5264298157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078894129/2000000000 : ℝ)|^1029 ≤ (43972017397089/100000000000000 : ℝ)^773
        have hw : |(1078894129/2000000000 : ℝ)|=(1078894129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s9_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312146307/10000000000 : ℝ)*x 0 + (-2153018947/10000000000 : ℝ)*x 1 + (2697235701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312146307/10000000000 : ℝ)^1029 ≤ (43080994109987/100000000000000 : ℝ)^773 := by
    have hnat : (5312146307 : ℕ)^1029*100000000000000^773 ≤ 43080994109987^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312146307 10000000000 43080994109987 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153018947/10000000000 : ℝ)^1029 ≤ (6473490127359/50000000000000 : ℝ)^773 := by
    have hnat : (2153018947 : ℕ)^1029*50000000000000^773 ≤ 6473490127359^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153018947 10000000000 6473490127359 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697235701/5000000000 : ℝ)^1029 ≤ (43972025611177/100000000000000 : ℝ)^773 := by
    have hnat : (2697235701 : ℕ)^1029*100000000000000^773 ≤ 43972025611177^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697235701 5000000000 43972025611177 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312146307/10000000000 : ℝ), (-2153018947/10000000000 : ℝ), (2697235701/5000000000 : ℝ)] ![(43080994109987/100000000000000 : ℝ), (6473490127359/50000000000000 : ℝ), (43972025611177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312146307/10000000000 : ℝ)|^1029 ≤ (43080994109987/100000000000000 : ℝ)^773
        have hw : |(5312146307/10000000000 : ℝ)|=(5312146307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153018947/10000000000 : ℝ)|^1029 ≤ (6473490127359/50000000000000 : ℝ)^773
        have hw : |(-2153018947/10000000000 : ℝ)|=(2153018947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697235701/5000000000 : ℝ)|^1029 ≤ (43972025611177/100000000000000 : ℝ)^773
        have hw : |(2697235701/5000000000 : ℝ)|=(2697235701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s9_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312147059/10000000000 : ℝ)*x 0 + (134861773/250000000 : ℝ)*x 1 + (-2153018587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312147059/10000000000 : ℝ)^1029 ≤ (2692562639273/6250000000000 : ℝ)^773 := by
    have hnat : (5312147059 : ℕ)^1029*6250000000000^773 ≤ 2692562639273^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312147059 10000000000 2692562639273 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134861773/250000000 : ℝ)^1029 ≤ (43972020381071/100000000000000 : ℝ)^773 := by
    have hnat : (134861773 : ℕ)^1029*100000000000000^773 ≤ 43972020381071^773*250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134861773 250000000 43972020381071 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153018587/10000000000 : ℝ)^1029 ≤ (12946977372951/100000000000000 : ℝ)^773 := by
    have hnat : (2153018587 : ℕ)^1029*100000000000000^773 ≤ 12946977372951^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153018587 10000000000 12946977372951 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312147059/10000000000 : ℝ), (134861773/250000000 : ℝ), (-2153018587/10000000000 : ℝ)] ![(2692562639273/6250000000000 : ℝ), (43972020381071/100000000000000 : ℝ), (12946977372951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312147059/10000000000 : ℝ)|^1029 ≤ (2692562639273/6250000000000 : ℝ)^773
        have hw : |(5312147059/10000000000 : ℝ)|=(5312147059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134861773/250000000 : ℝ)|^1029 ≤ (43972020381071/100000000000000 : ℝ)^773
        have hw : |(134861773/250000000 : ℝ)|=(134861773/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153018587/10000000000 : ℝ)|^1029 ≤ (12946977372951/100000000000000 : ℝ)^773
        have hw : |(-2153018587/10000000000 : ℝ)|=(2153018587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s9_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (875880073/2000000000 : ℝ)*x 0 + (4508162019/10000000000 : ℝ)*x 1 + (1063602147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875880073/2000000000 : ℝ)^1029 ≤ (66632996263/200000000000 : ℝ)^773 := by
    have hnat : (875880073 : ℕ)^1029*200000000000^773 ≤ 66632996263^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875880073 2000000000 66632996263 200000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508162019/10000000000 : ℝ)^1029 ≤ (4328346758613/12500000000000 : ℝ)^773 := by
    have hnat : (4508162019 : ℕ)^1029*12500000000000^773 ≤ 4328346758613^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508162019 10000000000 4328346758613 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063602147/2500000000 : ℝ)^1029 ≤ (6411345557083/20000000000000 : ℝ)^773 := by
    have hnat : (1063602147 : ℕ)^1029*20000000000000^773 ≤ 6411345557083^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063602147 2500000000 6411345557083 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875880073/2000000000 : ℝ), (4508162019/10000000000 : ℝ), (1063602147/2500000000 : ℝ)] ![(66632996263/200000000000 : ℝ), (4328346758613/12500000000000 : ℝ), (6411345557083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875880073/2000000000 : ℝ)|^1029 ≤ (66632996263/200000000000 : ℝ)^773
        have hw : |(875880073/2000000000 : ℝ)|=(875880073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508162019/10000000000 : ℝ)|^1029 ≤ (4328346758613/12500000000000 : ℝ)^773
        have hw : |(4508162019/10000000000 : ℝ)|=(4508162019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063602147/2500000000 : ℝ)|^1029 ≤ (6411345557083/20000000000000 : ℝ)^773
        have hw : |(1063602147/2500000000 : ℝ)|=(1063602147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2797/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6993/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6993/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6993/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6993/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6993/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6993/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (8231/2048 : ℝ) ≤ (15168646379887663/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^8231 ≤ (15168646379887663/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5607 : ℕ)^8231*100000000000000000000^2048 ≤ 15168646379887663^2048*50000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 15168646379887663 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (15168646379887663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6993/50000 : ℝ) ^ (8231/2048 : ℝ) ≤ (7371155274137493/20000000000000000000 : ℝ) := by
    have hpowers : (6993/50000 : ℝ)^8231 ≤ (7371155274137493/20000000000000000000 : ℝ)^2048 := by
      have hnat : (6993 : ℕ)^8231*20000000000000000000^2048 ≤ 7371155274137493^2048*50000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6993 50000 7371155274137493 20000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6993/50000 : ℝ)) (X := (7371155274137493/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015168646379887663/50000000000000000000 : ℝ) ≤ (10000754752731911/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50015168646379887663/50000000000000000000 : ℝ)^2048 ≤ (10000754752731911/10000000000000000 : ℝ)^8231 := by
      have hnat : (50015168646379887663 : ℕ)^2048*10000000000000000^8231 ≤ 10000754752731911^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015168646379887663 50000000000000000000 10000754752731911 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754752731911/10000000000000000 : ℝ)) (X := (50015168646379887663/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506503052843821891/12500000000000000000 : ℝ) ≤ (2500323548794351/2500000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (12506503052843821891/12500000000000000000 : ℝ)^2048 ≤ (2500323548794351/2500000000000000 : ℝ)^8231 := by
      have hnat : (12506503052843821891 : ℕ)^2048*2500000000000000^8231 ≤ 2500323548794351^8231*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506503052843821891 12500000000000000000 2500323548794351 2500000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500323548794351/2500000000000000 : ℝ)) (X := (12506503052843821891/12500000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007371155274137493/10000000000000000000 : ℝ) ≤ (10001833637622897/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (10007371155274137493/10000000000000000000 : ℝ)^2048 ≤ (10001833637622897/10000000000000000 : ℝ)^8231 := by
      have hnat : (10007371155274137493 : ℕ)^2048*10000000000000000^8231 ≤ 10001833637622897^8231*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007371155274137493 10000000000000000000 10001833637622897 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001833637622897/10000000000000000 : ℝ)) (X := (10007371155274137493/10000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15168646379887663/100000000000000000000 : ℝ) ≤ ((3436259121950067/3437500000000000 : ℝ)+2*(77063206499/39600000000000 : ℝ)*(5607/50000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (3436259121950067/3437500000000000 : ℝ)+2*(77063206499/39600000000000 : ℝ)*(5607/50000 : ℝ)=(10000754752731911/10000000000000000 : ℝ) by norm_num, show 1+2*(15168646379887663/100000000000000000000 : ℝ)=(50015168646379887663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7371155274137493/20000000000000000000 : ℝ)+(15168646379887663/100000000000000000000 : ℝ) ≤ ((3436259121950067/3437500000000000 : ℝ)+(77063206499/39600000000000 : ℝ)*((6993/50000 : ℝ)+(5607/50000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (3436259121950067/3437500000000000 : ℝ)+(77063206499/39600000000000 : ℝ)*((6993/50000 : ℝ)+(5607/50000 : ℝ))=(2500323548794351/2500000000000000 : ℝ) by norm_num, show 1+(7371155274137493/20000000000000000000 : ℝ)+(15168646379887663/100000000000000000000 : ℝ)=(12506503052843821891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7371155274137493/20000000000000000000 : ℝ) ≤ ((3436259121950067/3437500000000000 : ℝ)+2*(77063206499/39600000000000 : ℝ)*(6993/50000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (3436259121950067/3437500000000000 : ℝ)+2*(77063206499/39600000000000 : ℝ)*(6993/50000 : ℝ)=(10001833637622897/10000000000000000 : ℝ) by norm_num, show 1+2*(7371155274137493/20000000000000000000 : ℝ)=(10007371155274137493/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3436259121950067/3437500000000000 : ℝ)*(X 1 0+X 2 0)+(77063206499/39600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (6993/50000 : ℝ)) (c := (3436259121950067/3437500000000000 : ℝ)) (alpha := (77063206499/39600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3436259121950067/3437500000000000 : ℝ)*(X 0 1+X 2 1)+(77063206499/39600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (6993/50000 : ℝ)) (c := (3436259121950067/3437500000000000 : ℝ)) (alpha := (77063206499/39600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3436259121950067/3437500000000000 : ℝ)*(X 0 2+X 1 2)+(77063206499/39600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (6993/50000 : ℝ)) (c := (3436259121950067/3437500000000000 : ℝ)) (alpha := (77063206499/39600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336257119/2500000000 : ℝ)*X 2 0+(5263970827/10000000000 : ℝ)*X 2 1+(-570879747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1108569591/5000000000 : ℝ)*X 0 0+(5264298157/10000000000 : ℝ)*X 0 1+(1078894129/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312146307/10000000000 : ℝ)*X 1 0+(-2153018947/10000000000 : ℝ)*X 1 1+(2697235701/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312147059/10000000000 : ℝ)*X 2 0+(134861773/250000000 : ℝ)*X 2 1+(-2153018587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((875880073/2000000000 : ℝ)*X 0 0+(4508162019/10000000000 : ℝ)*X 0 1+(1063602147/2500000000 : ℝ)*X 0 2+(875880073/2000000000 : ℝ)*X 1 0+(4508162019/10000000000 : ℝ)*X 1 1+(1063602147/2500000000 : ℝ)*X 1 2+(875880073/2000000000 : ℝ)*X 2 0+(4508162019/10000000000 : ℝ)*X 2 1+(1063602147/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (169233952026949606529/60000000000000000000000000 : ℝ) := by norm_num
    linear_combination (593577419/50000000000000 : ℝ)*(base23) + (468459773/100000000000000 : ℝ)*(lower1) + (53712301/25000000000000 : ℝ)*(upper2) + (113074407/100000000000000 : ℝ)*(upper3) + (32472557/12500000000000 : ℝ)*(upper4) + (41032001/100000000000000 : ℝ)*(upper5) + (5811456568807879/100000000000000 : ℝ)*(major0) + (5811456568807879/100000000000000 : ℝ)*(major1) + (5811456568807879/100000000000000 : ℝ)*(major2) + (7441302067/25000000000000 : ℝ)*(sp0) + (3841044793703597/50000000000000 : ℝ)*(sp1) + (3841044793703597/50000000000000 : ℝ)*(sp2) + (960257329380511/12500000000000 : ℝ)*(sp3) + (1970411728094847/50000000000000 : ℝ)*(sp4) + (1970411728094847/50000000000000 : ℝ)*(f.failure) + (3841044793703597/50000000000000 : ℝ)*(f.sum) + (359614139849/180000000000000000000000000 : ℝ)*base66 + (7472759229406343/1125000000000000000000000000000 : ℝ)*base67 + (13258478351656343/1125000000000000000000000000000 : ℝ)*base69 + (12528837647593657/1125000000000000000000000000000 : ℝ)*base72 + (746096256271/180000000000000000000000000 : ℝ)*base73 + (6617173238593657/1125000000000000000000000000000 : ℝ)*base76 + (5354537374843657/1125000000000000000000000000000 : ℝ)*base78 + (11767584949156343/1125000000000000000000000000000 : ℝ)*base79 + (3362268786751/180000000000000000000000000 : ℝ)*base81 + (10699219/5000000000000000000000 : ℝ)*base89 + (10699219/5000000000000000000000 : ℝ)*base91 + (10699219/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1039_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_box_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-130420963/625000000 : ℝ)*x 0 + (5377728471/10000000000 : ℝ)*x 1 + (2688864309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130420963/625000000 : ℝ)^1029 ≤ (6209555059427/50000000000000 : ℝ)^773 := by
    have hnat : (130420963 : ℕ)^1029*50000000000000^773 ≤ 6209555059427^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130420963 625000000 6209555059427 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377728471/10000000000 : ℝ)^1029 ≤ (43790444139467/100000000000000 : ℝ)^773 := by
    have hnat : (5377728471 : ℕ)^1029*100000000000000^773 ≤ 43790444139467^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377728471 10000000000 43790444139467 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688864309/5000000000 : ℝ)^1029 ≤ (437904457329/1000000000000 : ℝ)^773 := by
    have hnat : (2688864309 : ℕ)^1029*1000000000000^773 ≤ 437904457329^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688864309 5000000000 437904457329 1000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130420963/625000000 : ℝ), (5377728471/10000000000 : ℝ), (2688864309/5000000000 : ℝ)] ![(6209555059427/50000000000000 : ℝ), (43790444139467/100000000000000 : ℝ), (437904457329/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130420963/625000000 : ℝ)|^1029 ≤ (6209555059427/50000000000000 : ℝ)^773
        have hw : |(-130420963/625000000 : ℝ)|=(130420963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377728471/10000000000 : ℝ)|^1029 ≤ (43790444139467/100000000000000 : ℝ)^773
        have hw : |(5377728471/10000000000 : ℝ)|=(5377728471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688864309/5000000000 : ℝ)|^1029 ≤ (437904457329/1000000000000 : ℝ)^773
        have hw : |(2688864309/5000000000 : ℝ)|=(2688864309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (661861059/1250000000 : ℝ)*x 0 + (-137425259/625000000 : ℝ)*x 1 + (2688864279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661861059/1250000000 : ℝ)^1029 ≤ (42894783673569/100000000000000 : ℝ)^773 := by
    have hnat : (661861059 : ℕ)^1029*100000000000000^773 ≤ 42894783673569^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661861059 1250000000 42894783673569 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137425259/625000000 : ℝ)^1029 ≤ (3328692803957/25000000000000 : ℝ)^773 := by
    have hnat : (137425259 : ℕ)^1029*25000000000000^773 ≤ 3328692803957^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137425259 625000000 3328692803957 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688864279/5000000000 : ℝ)^1029 ≤ (43790445082519/100000000000000 : ℝ)^773 := by
    have hnat : (2688864279 : ℕ)^1029*100000000000000^773 ≤ 43790445082519^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688864279 5000000000 43790445082519 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661861059/1250000000 : ℝ), (-137425259/625000000 : ℝ), (2688864279/5000000000 : ℝ)] ![(42894783673569/100000000000000 : ℝ), (3328692803957/25000000000000 : ℝ), (43790445082519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661861059/1250000000 : ℝ)|^1029 ≤ (42894783673569/100000000000000 : ℝ)^773
        have hw : |(661861059/1250000000 : ℝ)|=(661861059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137425259/625000000 : ℝ)|^1029 ≤ (3328692803957/25000000000000 : ℝ)^773
        have hw : |(-137425259/625000000 : ℝ)|=(137425259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688864279/5000000000 : ℝ)|^1029 ≤ (43790445082519/100000000000000 : ℝ)^773
        have hw : |(2688864279/5000000000 : ℝ)|=(2688864279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2647444187/5000000000 : ℝ)*x 0 + (1075545699/2000000000 : ℝ)*x 1 + (-1099402181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647444187/5000000000 : ℝ)^1029 ≤ (5361847827091/12500000000000 : ℝ)^773 := by
    have hnat : (2647444187 : ℕ)^1029*12500000000000^773 ≤ 5361847827091^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647444187 5000000000 5361847827091 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075545699/2000000000 : ℝ)^1029 ≤ (43790444399619/100000000000000 : ℝ)^773 := by
    have hnat : (1075545699 : ℕ)^1029*100000000000000^773 ≤ 43790444399619^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075545699 2000000000 43790444399619 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099402181/5000000000 : ℝ)^1029 ≤ (6657386486551/50000000000000 : ℝ)^773 := by
    have hnat : (1099402181 : ℕ)^1029*50000000000000^773 ≤ 6657386486551^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099402181 5000000000 6657386486551 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647444187/5000000000 : ℝ), (1075545699/2000000000 : ℝ), (-1099402181/5000000000 : ℝ)] ![(5361847827091/12500000000000 : ℝ), (43790444399619/100000000000000 : ℝ), (6657386486551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647444187/5000000000 : ℝ)|^1029 ≤ (5361847827091/12500000000000 : ℝ)^773
        have hw : |(2647444187/5000000000 : ℝ)|=(2647444187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075545699/2000000000 : ℝ)|^1029 ≤ (43790444399619/100000000000000 : ℝ)^773
        have hw : |(1075545699/2000000000 : ℝ)|=(1075545699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099402181/5000000000 : ℝ)|^1029 ≤ (6657386486551/50000000000000 : ℝ)^773
        have hw : |(-1099402181/5000000000 : ℝ)|=(1099402181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (280505641/625000000 : ℝ)*x 0 + (216361183/500000000 : ℝ)*x 1 + (3461779/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280505641/625000000 : ℝ)^1029 ≤ (34421698796493/100000000000000 : ℝ)^773 := by
    have hnat : (280505641 : ℕ)^1029*100000000000000^773 ≤ 34421698796493^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280505641 625000000 34421698796493 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216361183/500000000 : ℝ)^1029 ≤ (32789150142341/100000000000000 : ℝ)^773 := by
    have hnat : (216361183 : ℕ)^1029*100000000000000^773 ≤ 32789150142341^773*500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216361183 500000000 32789150142341 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3461779/8000000 : ℝ)^1029 ≤ (409864388127/1250000000000 : ℝ)^773 := by
    have hnat : (3461779 : ℕ)^1029*1250000000000^773 ≤ 409864388127^773*8000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3461779 8000000 409864388127 1250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280505641/625000000 : ℝ), (216361183/500000000 : ℝ), (3461779/8000000 : ℝ)] ![(34421698796493/100000000000000 : ℝ), (32789150142341/100000000000000 : ℝ), (409864388127/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280505641/625000000 : ℝ)|^1029 ≤ (34421698796493/100000000000000 : ℝ)^773
        have hw : |(280505641/625000000 : ℝ)|=(280505641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216361183/500000000 : ℝ)|^1029 ≤ (32789150142341/100000000000000 : ℝ)^773
        have hw : |(216361183/500000000 : ℝ)|=(216361183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3461779/8000000 : ℝ)|^1029 ≤ (409864388127/1250000000000 : ℝ)^773
        have hw : |(3461779/8000000 : ℝ)|=(3461779/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2348925899/10000000000 : ℝ)*x 0 + (5279677489/10000000000 : ℝ)*x 1 + (5279676101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2348925899/10000000000 : ℝ)^1029 ≤ (14538364674501/100000000000000 : ℝ)^773 := by
    have hnat : (2348925899 : ℕ)^1029*100000000000000^773 ≤ 14538364674501^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348925899 10000000000 14538364674501 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279677489/10000000000 : ℝ)^1029 ≤ (21365412564903/50000000000000 : ℝ)^773 := by
    have hnat : (5279677489 : ℕ)^1029*50000000000000^773 ≤ 21365412564903^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279677489 10000000000 21365412564903 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279676101/10000000000 : ℝ)^1029 ≤ (42730810175743/100000000000000 : ℝ)^773 := by
    have hnat : (5279676101 : ℕ)^1029*100000000000000^773 ≤ 42730810175743^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279676101 10000000000 42730810175743 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2348925899/10000000000 : ℝ), (5279677489/10000000000 : ℝ), (5279676101/10000000000 : ℝ)] ![(14538364674501/100000000000000 : ℝ), (21365412564903/50000000000000 : ℝ), (42730810175743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2348925899/10000000000 : ℝ)|^1029 ≤ (14538364674501/100000000000000 : ℝ)^773
        have hw : |(-2348925899/10000000000 : ℝ)|=(2348925899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279677489/10000000000 : ℝ)|^1029 ≤ (21365412564903/50000000000000 : ℝ)^773
        have hw : |(5279677489/10000000000 : ℝ)|=(5279677489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279676101/10000000000 : ℝ)|^1029 ≤ (42730810175743/100000000000000 : ℝ)^773
        have hw : |(5279676101/10000000000 : ℝ)|=(5279676101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (268216223/500000000 : ℝ)*x 0 + (-1118526353/5000000000 : ℝ)*x 1 + (659959599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268216223/500000000 : ℝ)^1029 ≤ (43645208984369/100000000000000 : ℝ)^773 := by
    have hnat : (268216223 : ℕ)^1029*100000000000000^773 ≤ 43645208984369^773*500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268216223 500000000 43645208984369 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118526353/5000000000 : ℝ)^1029 ≤ (13623973371791/100000000000000 : ℝ)^773 := by
    have hnat : (1118526353 : ℕ)^1029*100000000000000^773 ≤ 13623973371791^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118526353 5000000000 13623973371791 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659959599/1250000000 : ℝ)^1029 ≤ (42730817620453/100000000000000 : ℝ)^773 := by
    have hnat : (659959599 : ℕ)^1029*100000000000000^773 ≤ 42730817620453^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659959599 1250000000 42730817620453 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268216223/500000000 : ℝ), (-1118526353/5000000000 : ℝ), (659959599/1250000000 : ℝ)] ![(43645208984369/100000000000000 : ℝ), (13623973371791/100000000000000 : ℝ), (42730817620453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268216223/500000000 : ℝ)|^1029 ≤ (43645208984369/100000000000000 : ℝ)^773
        have hw : |(268216223/500000000 : ℝ)|=(268216223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118526353/5000000000 : ℝ)|^1029 ≤ (13623973371791/100000000000000 : ℝ)^773
        have hw : |(-1118526353/5000000000 : ℝ)|=(1118526353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659959599/1250000000 : ℝ)|^1029 ≤ (42730817620453/100000000000000 : ℝ)^773
        have hw : |(659959599/1250000000 : ℝ)|=(659959599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (670540547/1250000000 : ℝ)*x 0 + (5279676553/10000000000 : ℝ)*x 1 + (-1118526569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670540547/1250000000 : ℝ)^1029 ≤ (10911302018647/25000000000000 : ℝ)^773 := by
    have hnat : (670540547 : ℕ)^1029*25000000000000^773 ≤ 10911302018647^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670540547 1250000000 10911302018647 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279676553/10000000000 : ℝ)^1029 ≤ (4273081504551/10000000000000 : ℝ)^773 := by
    have hnat : (5279676553 : ℕ)^1029*10000000000000^773 ≤ 4273081504551^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279676553 10000000000 4273081504551 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118526569/5000000000 : ℝ)^1029 ≤ (13623976874041/100000000000000 : ℝ)^773 := by
    have hnat : (1118526569 : ℕ)^1029*100000000000000^773 ≤ 13623976874041^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118526569 5000000000 13623976874041 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670540547/1250000000 : ℝ), (5279676553/10000000000 : ℝ), (-1118526569/5000000000 : ℝ)] ![(10911302018647/25000000000000 : ℝ), (4273081504551/10000000000000 : ℝ), (13623976874041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670540547/1250000000 : ℝ)|^1029 ≤ (10911302018647/25000000000000 : ℝ)^773
        have hw : |(670540547/1250000000 : ℝ)|=(670540547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279676553/10000000000 : ℝ)|^1029 ≤ (4273081504551/10000000000000 : ℝ)^773
        have hw : |(5279676553/10000000000 : ℝ)|=(5279676553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1118526569/5000000000 : ℝ)|^1029 ≤ (13623976874041/100000000000000 : ℝ)^773
        have hw : |(-1118526569/5000000000 : ℝ)|=(1118526569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2135187271/5000000000 : ℝ)*x 0 + (2218030151/5000000000 : ℝ)*x 1 + (55450743/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135187271/5000000000 : ℝ)^1029 ≤ (6443394249393/20000000000000 : ℝ)^773 := by
    have hnat : (2135187271 : ℕ)^1029*20000000000000^773 ≤ 6443394249393^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135187271 5000000000 6443394249393 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218030151/5000000000 : ℝ)^1029 ≤ (33891518753239/100000000000000 : ℝ)^773 := by
    have hnat : (2218030151 : ℕ)^1029*100000000000000^773 ≤ 33891518753239^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218030151 5000000000 33891518753239 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55450743/125000000 : ℝ)^1029 ≤ (33891509986527/100000000000000 : ℝ)^773 := by
    have hnat : (55450743 : ℕ)^1029*100000000000000^773 ≤ 33891509986527^773*125000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55450743 125000000 33891509986527 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135187271/5000000000 : ℝ), (2218030151/5000000000 : ℝ), (55450743/125000000 : ℝ)] ![(6443394249393/20000000000000 : ℝ), (33891518753239/100000000000000 : ℝ), (33891509986527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135187271/5000000000 : ℝ)|^1029 ≤ (6443394249393/20000000000000 : ℝ)^773
        have hw : |(2135187271/5000000000 : ℝ)|=(2135187271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2218030151/5000000000 : ℝ)|^1029 ≤ (33891518753239/100000000000000 : ℝ)^773
        have hw : |(2218030151/5000000000 : ℝ)|=(2218030151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55450743/125000000 : ℝ)|^1029 ≤ (33891509986527/100000000000000 : ℝ)^773
        have hw : |(55450743/125000000 : ℝ)|=(55450743/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_8 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1147113027/5000000000 : ℝ)*x 0 + (1042639283/2000000000 : ℝ)*x 1 + (1077465047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147113027/5000000000 : ℝ)^1029 ≤ (14089431718131/100000000000000 : ℝ)^773 := by
    have hnat : (1147113027 : ℕ)^1029*100000000000000^773 ≤ 14089431718131^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147113027 5000000000 14089431718131 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042639283/2000000000 : ℝ)^1029 ≤ (10504016895209/25000000000000 : ℝ)^773 := by
    have hnat : (1042639283 : ℕ)^1029*25000000000000^773 ≤ 10504016895209^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042639283 2000000000 10504016895209 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077465047/2000000000 : ℝ)^1029 ≤ (43894500693411/100000000000000 : ℝ)^773 := by
    have hnat : (1077465047 : ℕ)^1029*100000000000000^773 ≤ 43894500693411^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077465047 2000000000 43894500693411 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1147113027/5000000000 : ℝ), (1042639283/2000000000 : ℝ), (1077465047/2000000000 : ℝ)] ![(14089431718131/100000000000000 : ℝ), (10504016895209/25000000000000 : ℝ), (43894500693411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1147113027/5000000000 : ℝ)|^1029 ≤ (14089431718131/100000000000000 : ℝ)^773
        have hw : |(-1147113027/5000000000 : ℝ)|=(1147113027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042639283/2000000000 : ℝ)|^1029 ≤ (10504016895209/25000000000000 : ℝ)^773
        have hw : |(1042639283/2000000000 : ℝ)|=(1042639283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077465047/2000000000 : ℝ)|^1029 ≤ (43894500693411/100000000000000 : ℝ)^773
        have hw : |(1077465047/2000000000 : ℝ)|=(1077465047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_9 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5288088437/10000000000 : ℝ)*x 0 + (-2194989973/10000000000 : ℝ)*x 1 + (538732503/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288088437/10000000000 : ℝ)^1029 ≤ (21410733538123/50000000000000 : ℝ)^773 := by
    have hnat : (5288088437 : ℕ)^1029*50000000000000^773 ≤ 21410733538123^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288088437 10000000000 21410733538123 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194989973/10000000000 : ℝ)^1029 ≤ (2656806886869/20000000000000 : ℝ)^773 := by
    have hnat : (2194989973 : ℕ)^1029*20000000000000^773 ≤ 2656806886869^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194989973 10000000000 2656806886869 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538732503/1000000000 : ℝ)^1029 ≤ (10973624617491/25000000000000 : ℝ)^773 := by
    have hnat : (538732503 : ℕ)^1029*25000000000000^773 ≤ 10973624617491^773*1000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538732503 1000000000 10973624617491 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288088437/10000000000 : ℝ), (-2194989973/10000000000 : ℝ), (538732503/1000000000 : ℝ)] ![(21410733538123/50000000000000 : ℝ), (2656806886869/20000000000000 : ℝ), (10973624617491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288088437/10000000000 : ℝ)|^1029 ≤ (21410733538123/50000000000000 : ℝ)^773
        have hw : |(5288088437/10000000000 : ℝ)|=(5288088437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194989973/10000000000 : ℝ)|^1029 ≤ (2656806886869/20000000000000 : ℝ)^773
        have hw : |(-2194989973/10000000000 : ℝ)|=(2194989973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538732503/1000000000 : ℝ)|^1029 ≤ (10973624617491/25000000000000 : ℝ)^773
        have hw : |(538732503/1000000000 : ℝ)|=(538732503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_10 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (211523549/400000000 : ℝ)*x 0 + (5387325151/10000000000 : ℝ)*x 1 + (-1097494713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211523549/400000000 : ℝ)^1029 ≤ (21410735090371/50000000000000 : ℝ)^773 := by
    have hnat : (211523549 : ℕ)^1029*50000000000000^773 ≤ 21410735090371^773*400000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211523549 400000000 21410735090371 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387325151/10000000000 : ℝ)^1029 ≤ (2194724989117/5000000000000 : ℝ)^773 := by
    have hnat : (5387325151 : ℕ)^1029*5000000000000^773 ≤ 2194724989117^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387325151 10000000000 2194724989117 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097494713/5000000000 : ℝ)^1029 ≤ (3321007506893/25000000000000 : ℝ)^773 := by
    have hnat : (1097494713 : ℕ)^1029*25000000000000^773 ≤ 3321007506893^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097494713 5000000000 3321007506893 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211523549/400000000 : ℝ), (5387325151/10000000000 : ℝ), (-1097494713/5000000000 : ℝ)] ![(21410735090371/50000000000000 : ℝ), (2194724989117/5000000000000 : ℝ), (3321007506893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211523549/400000000 : ℝ)|^1029 ≤ (21410735090371/50000000000000 : ℝ)^773
        have hw : |(211523549/400000000 : ℝ)|=(211523549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387325151/10000000000 : ℝ)|^1029 ≤ (2194724989117/5000000000000 : ℝ)^773
        have hw : |(5387325151/10000000000 : ℝ)|=(5387325151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097494713/5000000000 : ℝ)|^1029 ≤ (3321007506893/25000000000000 : ℝ)^773
        have hw : |(-1097494713/5000000000 : ℝ)|=(1097494713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_11 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4509125033/10000000000 : ℝ)*x 0 + (4316565693/10000000000 : ℝ)*x 1 + (4316565917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509125033/10000000000 : ℝ)^1029 ≤ (34636620897091/100000000000000 : ℝ)^773 := by
    have hnat : (4509125033 : ℕ)^1029*100000000000000^773 ≤ 34636620897091^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509125033 10000000000 34636620897091 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316565693/10000000000 : ℝ)^1029 ≤ (1021302763017/3125000000000 : ℝ)^773 := by
    have hnat : (4316565693 : ℕ)^1029*3125000000000^773 ≤ 1021302763017^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316565693 10000000000 1021302763017 3125000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316565917/10000000000 : ℝ)^1029 ≤ (408521133427/1250000000000 : ℝ)^773 := by
    have hnat : (4316565917 : ℕ)^1029*1250000000000^773 ≤ 408521133427^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316565917 10000000000 408521133427 1250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509125033/10000000000 : ℝ), (4316565693/10000000000 : ℝ), (4316565917/10000000000 : ℝ)] ![(34636620897091/100000000000000 : ℝ), (1021302763017/3125000000000 : ℝ), (408521133427/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509125033/10000000000 : ℝ)|^1029 ≤ (34636620897091/100000000000000 : ℝ)^773
        have hw : |(4509125033/10000000000 : ℝ)|=(4509125033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316565693/10000000000 : ℝ)|^1029 ≤ (1021302763017/3125000000000 : ℝ)^773
        have hw : |(4316565693/10000000000 : ℝ)|=(4316565693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316565917/10000000000 : ℝ)|^1029 ≤ (408521133427/1250000000000 : ℝ)^773
        have hw : |(4316565917/10000000000 : ℝ)|=(4316565917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_12 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141822163/10000000000 : ℝ)*x 0 + (2721425919/5000000000 : ℝ)*x 1 + (2635845401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141822163/10000000000 : ℝ)^1029 ≤ (12857428267261/100000000000000 : ℝ)^773 := by
    have hnat : (2141822163 : ℕ)^1029*100000000000000^773 ≤ 12857428267261^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141822163 10000000000 12857428267261 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721425919/5000000000 : ℝ)^1029 ≤ (11124443042523/25000000000000 : ℝ)^773 := by
    have hnat : (2721425919 : ℕ)^1029*25000000000000^773 ≤ 11124443042523^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721425919 5000000000 11124443042523 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635845401/5000000000 : ℝ)^1029 ≤ (10661199888229/25000000000000 : ℝ)^773 := by
    have hnat : (2635845401 : ℕ)^1029*25000000000000^773 ≤ 10661199888229^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635845401 5000000000 10661199888229 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141822163/10000000000 : ℝ), (2721425919/5000000000 : ℝ), (2635845401/5000000000 : ℝ)] ![(12857428267261/100000000000000 : ℝ), (11124443042523/25000000000000 : ℝ), (10661199888229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141822163/10000000000 : ℝ)|^1029 ≤ (12857428267261/100000000000000 : ℝ)^773
        have hw : |(-2141822163/10000000000 : ℝ)|=(2141822163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721425919/5000000000 : ℝ)|^1029 ≤ (11124443042523/25000000000000 : ℝ)^773
        have hw : |(2721425919/5000000000 : ℝ)|=(2721425919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635845401/5000000000 : ℝ)|^1029 ≤ (10661199888229/25000000000000 : ℝ)^773
        have hw : |(2635845401/5000000000 : ℝ)|=(2635845401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_13 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1073995513/2000000000 : ℝ)*x 0 + (-1120054331/5000000000 : ℝ)*x 1 + (5271690779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073995513/2000000000 : ℝ)^1029 ≤ (21853223438239/50000000000000 : ℝ)^773 := by
    have hnat : (1073995513 : ℕ)^1029*50000000000000^773 ≤ 21853223438239^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073995513 2000000000 21853223438239 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120054331/5000000000 : ℝ)^1029 ≤ (6824376898263/50000000000000 : ℝ)^773 := by
    have hnat : (1120054331 : ℕ)^1029*50000000000000^773 ≤ 6824376898263^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120054331 5000000000 6824376898263 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271690779/10000000000 : ℝ)^1029 ≤ (21322399652621/50000000000000 : ℝ)^773 := by
    have hnat : (5271690779 : ℕ)^1029*50000000000000^773 ≤ 21322399652621^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271690779 10000000000 21322399652621 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073995513/2000000000 : ℝ), (-1120054331/5000000000 : ℝ), (5271690779/10000000000 : ℝ)] ![(21853223438239/50000000000000 : ℝ), (6824376898263/50000000000000 : ℝ), (21322399652621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073995513/2000000000 : ℝ)|^1029 ≤ (21853223438239/50000000000000 : ℝ)^773
        have hw : |(1073995513/2000000000 : ℝ)|=(1073995513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120054331/5000000000 : ℝ)|^1029 ≤ (6824376898263/50000000000000 : ℝ)^773
        have hw : |(-1120054331/5000000000 : ℝ)|=(1120054331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271690779/10000000000 : ℝ)|^1029 ≤ (21322399652621/50000000000000 : ℝ)^773
        have hw : |(5271690779/10000000000 : ℝ)|=(5271690779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_14 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342494351/2500000000 : ℝ)*x 0 + (1054338191/2000000000 : ℝ)*x 1 + (-560027161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342494351/2500000000 : ℝ)^1029 ≤ (43706445132123/100000000000000 : ℝ)^773 := by
    have hnat : (1342494351 : ℕ)^1029*100000000000000^773 ≤ 43706445132123^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342494351 2500000000 43706445132123 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054338191/2000000000 : ℝ)^1029 ≤ (10661200300121/25000000000000 : ℝ)^773 := by
    have hnat : (1054338191 : ℕ)^1029*25000000000000^773 ≤ 10661200300121^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054338191 2000000000 10661200300121 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560027161/2500000000 : ℝ)^1029 ≤ (3412188412633/25000000000000 : ℝ)^773 := by
    have hnat : (560027161 : ℕ)^1029*25000000000000^773 ≤ 3412188412633^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560027161 2500000000 3412188412633 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342494351/2500000000 : ℝ), (1054338191/2000000000 : ℝ), (-560027161/2500000000 : ℝ)] ![(43706445132123/100000000000000 : ℝ), (10661200300121/25000000000000 : ℝ), (3412188412633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342494351/2500000000 : ℝ)|^1029 ≤ (43706445132123/100000000000000 : ℝ)^773
        have hw : |(1342494351/2500000000 : ℝ)|=(1342494351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054338191/2000000000 : ℝ)|^1029 ≤ (10661200300121/25000000000000 : ℝ)^773
        have hw : |(1054338191/2000000000 : ℝ)|=(1054338191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560027161/2500000000 : ℝ)|^1029 ≤ (3412188412633/25000000000000 : ℝ)^773
        have hw : |(-560027161/2500000000 : ℝ)|=(560027161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_box_15 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2126206311/5000000000 : ℝ)*x 0 + (138903727/312500000 : ℝ)*x 1 + (1111229791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126206311/5000000000 : ℝ)^1029 ≤ (1281468364527/4000000000000 : ℝ)^773 := by
    have hnat : (2126206311 : ℕ)^1029*4000000000000^773 ≤ 1281468364527^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126206311 5000000000 1281468364527 4000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138903727/312500000 : ℝ)^1029 ≤ (33981645944529/100000000000000 : ℝ)^773 := by
    have hnat : (138903727 : ℕ)^1029*100000000000000^773 ≤ 33981645944529^773*312500000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138903727 312500000 33981645944529 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111229791/2500000000 : ℝ)^1029 ≤ (33981644926837/100000000000000 : ℝ)^773 := by
    have hnat : (1111229791 : ℕ)^1029*100000000000000^773 ≤ 33981644926837^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111229791 2500000000 33981644926837 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126206311/5000000000 : ℝ), (138903727/312500000 : ℝ), (1111229791/2500000000 : ℝ)] ![(1281468364527/4000000000000 : ℝ), (33981645944529/100000000000000 : ℝ), (33981644926837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126206311/5000000000 : ℝ)|^1029 ≤ (1281468364527/4000000000000 : ℝ)^773
        have hw : |(2126206311/5000000000 : ℝ)|=(2126206311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138903727/312500000 : ℝ)|^1029 ≤ (33981645944529/100000000000000 : ℝ)^773
        have hw : |(138903727/312500000 : ℝ)|=(138903727/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1111229791/2500000000 : ℝ)|^1029 ≤ (33981644926837/100000000000000 : ℝ)^773
        have hw : |(1111229791/2500000000 : ℝ)|=(1111229791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59221/100000 : ℝ) ∧ (79487/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82891/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2797/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2797/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2797/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2797/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2797/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2797/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (8231/2048 : ℝ) ≤ (15168646379887663/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^8231 ≤ (15168646379887663/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5607 : ℕ)^8231*100000000000000000000^2048 ≤ 15168646379887663^2048*50000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 15168646379887663 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (15168646379887663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2797/20000 : ℝ) ^ (8231/2048 : ℝ) ≤ (18422593284643333/50000000000000000000 : ℝ) := by
    have hpowers : (2797/20000 : ℝ)^8231 ≤ (18422593284643333/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2797 : ℕ)^8231*50000000000000000000^2048 ≤ 18422593284643333^2048*20000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2797 20000 18422593284643333 50000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2797/20000 : ℝ)) (X := (18422593284643333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015168646379887663/50000000000000000000 : ℝ) ≤ (10000754752731911/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50015168646379887663/50000000000000000000 : ℝ)^2048 ≤ (10000754752731911/10000000000000000 : ℝ)^8231 := by
      have hnat : (50015168646379887663 : ℕ)^2048*10000000000000000^8231 ≤ 10000754752731911^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015168646379887663 50000000000000000000 10000754752731911 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754752731911/10000000000000000 : ℝ)) (X := (50015168646379887663/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052013832949174329/100000000000000000000 : ℝ) ≤ (2000258786357939/2000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (100052013832949174329/100000000000000000000 : ℝ)^2048 ≤ (2000258786357939/2000000000000000 : ℝ)^8231 := by
      have hnat : (100052013832949174329 : ℕ)^2048*2000000000000000^8231 ≤ 2000258786357939^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052013832949174329 100000000000000000000 2000258786357939 2000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000258786357939/2000000000000000 : ℝ)) (X := (100052013832949174329/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018422593284643333/25000000000000000000 : ℝ) ≤ (10001833110847479/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (25018422593284643333/25000000000000000000 : ℝ)^2048 ≤ (10001833110847479/10000000000000000 : ℝ)^8231 := by
      have hnat : (25018422593284643333 : ℕ)^2048*10000000000000000^8231 ≤ 10001833110847479^8231*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018422593284643333 25000000000000000000 10001833110847479 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001833110847479/10000000000000000 : ℝ)) (X := (25018422593284643333/25000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15168646379887663/100000000000000000000 : ℝ) ≤ ((27699998711912145829/27710000000000000000 : ℝ)+2*(67397382223/34637500000000 : ℝ)*(5607/50000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (27699998711912145829/27710000000000000000 : ℝ)+2*(67397382223/34637500000000 : ℝ)*(5607/50000 : ℝ)=(10000754752731911/10000000000000000 : ℝ) by norm_num, show 1+2*(15168646379887663/100000000000000000000 : ℝ)=(50015168646379887663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18422593284643333/50000000000000000000 : ℝ)+(15168646379887663/100000000000000000000 : ℝ) ≤ ((27699998711912145829/27710000000000000000 : ℝ)+(67397382223/34637500000000 : ℝ)*((2797/20000 : ℝ)+(5607/50000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (27699998711912145829/27710000000000000000 : ℝ)+(67397382223/34637500000000 : ℝ)*((2797/20000 : ℝ)+(5607/50000 : ℝ))=(2000258786357939/2000000000000000 : ℝ) by norm_num, show 1+(18422593284643333/50000000000000000000 : ℝ)+(15168646379887663/100000000000000000000 : ℝ)=(100052013832949174329/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18422593284643333/50000000000000000000 : ℝ) ≤ ((27699998711912145829/27710000000000000000 : ℝ)+2*(67397382223/34637500000000 : ℝ)*(2797/20000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (27699998711912145829/27710000000000000000 : ℝ)+2*(67397382223/34637500000000 : ℝ)*(2797/20000 : ℝ)=(10001833110847479/10000000000000000 : ℝ) by norm_num, show 1+2*(18422593284643333/50000000000000000000 : ℝ)=(25018422593284643333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27699998711912145829/27710000000000000000 : ℝ)*(X 1 0+X 2 0)+(67397382223/34637500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (27699998711912145829/27710000000000000000 : ℝ)) (alpha := (67397382223/34637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27699998711912145829/27710000000000000000 : ℝ)*(X 0 1+X 2 1)+(67397382223/34637500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (27699998711912145829/27710000000000000000 : ℝ)) (alpha := (67397382223/34637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27699998711912145829/27710000000000000000 : ℝ)*(X 0 2+X 1 2)+(67397382223/34637500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (27699998711912145829/27710000000000000000 : ℝ)) (alpha := (67397382223/34637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130420963/625000000 : ℝ)*X 0 0+(5377728471/10000000000 : ℝ)*X 0 1+(2688864309/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661861059/1250000000 : ℝ)*X 1 0+(-137425259/625000000 : ℝ)*X 1 1+(2688864279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647444187/5000000000 : ℝ)*X 2 0+(1075545699/2000000000 : ℝ)*X 2 1+(-1099402181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((280505641/625000000 : ℝ)*X 0 0+(216361183/500000000 : ℝ)*X 0 1+(3461779/8000000 : ℝ)*X 0 2+(280505641/625000000 : ℝ)*X 1 0+(216361183/500000000 : ℝ)*X 1 1+(3461779/8000000 : ℝ)*X 1 2+(280505641/625000000 : ℝ)*X 2 0+(216361183/500000000 : ℝ)*X 2 1+(3461779/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2348925899/10000000000 : ℝ)*X 0 0+(5279677489/10000000000 : ℝ)*X 0 1+(5279676101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268216223/500000000 : ℝ)*X 1 0+(-1118526353/5000000000 : ℝ)*X 1 1+(659959599/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((670540547/1250000000 : ℝ)*X 2 0+(5279676553/10000000000 : ℝ)*X 2 1+(-1118526569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135187271/5000000000 : ℝ)*X 0 0+(2218030151/5000000000 : ℝ)*X 0 1+(55450743/125000000 : ℝ)*X 0 2+(2135187271/5000000000 : ℝ)*X 1 0+(2218030151/5000000000 : ℝ)*X 1 1+(55450743/125000000 : ℝ)*X 1 2+(2135187271/5000000000 : ℝ)*X 2 0+(2218030151/5000000000 : ℝ)*X 2 1+(55450743/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1147113027/5000000000 : ℝ)*X 0 0+(1042639283/2000000000 : ℝ)*X 0 1+(1077465047/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288088437/10000000000 : ℝ)*X 1 0+(-2194989973/10000000000 : ℝ)*X 1 1+(538732503/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((211523549/400000000 : ℝ)*X 2 0+(5387325151/10000000000 : ℝ)*X 2 1+(-1097494713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4509125033/10000000000 : ℝ)*X 0 0+(4316565693/10000000000 : ℝ)*X 0 1+(4316565917/10000000000 : ℝ)*X 0 2+(4509125033/10000000000 : ℝ)*X 1 0+(4316565693/10000000000 : ℝ)*X 1 1+(4316565917/10000000000 : ℝ)*X 1 2+(4509125033/10000000000 : ℝ)*X 2 0+(4316565693/10000000000 : ℝ)*X 2 1+(4316565917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2141822163/10000000000 : ℝ)*X 0 0+(2721425919/5000000000 : ℝ)*X 0 1+(2635845401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073995513/2000000000 : ℝ)*X 1 0+(-1120054331/5000000000 : ℝ)*X 1 1+(5271690779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342494351/2500000000 : ℝ)*X 2 0+(1054338191/2000000000 : ℝ)*X 2 1+(-560027161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2126206311/5000000000 : ℝ)*X 0 0+(138903727/312500000 : ℝ)*X 0 1+(1111229791/2500000000 : ℝ)*X 0 2+(2126206311/5000000000 : ℝ)*X 1 0+(138903727/312500000 : ℝ)*X 1 1+(1111229791/2500000000 : ℝ)*X 1 2+(2126206311/5000000000 : ℝ)*X 2 0+(138903727/312500000 : ℝ)*X 2 1+(1111229791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-431035215888943526432257407707961/692750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29631201/100000000000000 : ℝ)*(upper0) + (2594329/100000000000000 : ℝ)*(upper1) + (61812473/12500000000000 : ℝ)*(upper3) + (1916879211615501/50000000000000 : ℝ)*(major0) + (1916879211615501/50000000000000 : ℝ)*(major1) + (1916879211615501/50000000000000 : ℝ)*(major2) + (37429412629/100000000000000 : ℝ)*(sp1) + (31273563323/100000000000000 : ℝ)*(sp2) + (24824252591/100000000000000 : ℝ)*(sp3) + (1272128794877941/25000000000000 : ℝ)*(sp4) + (1272124702648409/25000000000000 : ℝ)*(sp5) + (2544252483221471/50000000000000 : ℝ)*(sp6) + (1299848039444861/50000000000000 : ℝ)*(sp7) + (42120989/200000000000 : ℝ)*(sp8) + (2599720903142313/100000000000000 : ℝ)*(f.failure) + (1017707248001253/20000000000000 : ℝ)*(f.sum) + (2730173768469/1731875000000000000000000000 : ℝ)*base66 + (13731399078967295329/1385500000000000000000000000000000 : ℝ)*base67 + (29189485766080295329/1385500000000000000000000000000000 : ℝ)*base69 + (6746618535353295329/1385500000000000000000000000000000 : ℝ)*base71 + (365426143649/1731875000000000000000000000 : ℝ)*base74 + (13667181952015295329/1385500000000000000000000000000000 : ℝ)*base75 + (11525469138370295329/1385500000000000000000000000000000 : ℝ)*base77 + (6741510408834795329/1385500000000000000000000000000000 : ℝ)*base79 + (2726092525527/216484375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (44557899/10000000000000000000000 : ℝ)*base90 + (44557899/10000000000000000000000 : ℝ)*base92 + (44557899/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59221/100000 : ℝ) ≤ (102567361491621129884188695729159/173187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12561797/100000000000000 : ℝ)*(lower0) + (22672741/20000000000000 : ℝ)*(upper2) + (40608809/100000000000000 : ℝ)*(lower5) + (487025556510257/12500000000000 : ℝ)*(major0) + (487025556510257/12500000000000 : ℝ)*(major1) + (487025556510257/12500000000000 : ℝ)*(major2) + (5130592083427167/100000000000000 : ℝ)*(sp0) + (5130594460570199/100000000000000 : ℝ)*(sp1) + (2565289990105789/50000000000000 : ℝ)*(sp2) + (2642061284198227/100000000000000 : ℝ)*(sp3) + (1745826419/25000000000000 : ℝ)*(sp5) + (202975819/4000000000000 : ℝ)*(sp7) + (10731832149/50000000000000 : ℝ)*(sp10) + (9360448707/100000000000000 : ℝ)*(sp12) + (1321033179296851/50000000000000 : ℝ)*(f.failure) + (41044811551007/800000000000 : ℝ)*(f.sum) + (58300934644271/13855000000000000000000000000 : ℝ)*base66 + (10818760037266693053/346375000000000000000000000000000 : ℝ)*base67 + (617027706345818053/346375000000000000000000000000000 : ℝ)*base69 + (2750177529351681947/346375000000000000000000000000000 : ℝ)*base72 + (40300065018093/6927500000000000000000000000 : ℝ)*base74 + (202445739778431947/346375000000000000000000000000000 : ℝ)*base76 + (3164356590415931947/346375000000000000000000000000000 : ℝ)*base78 + (176993652412681947/346375000000000000000000000000000 : ℝ)*base80 + (27444035707237/6927500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (29125527/5000000000000000000000 : ℝ)*base89 + (29125527/5000000000000000000000 : ℝ)*base91 + (29125527/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79487/100000 : ℝ) ≤ (275331109669046202376206249086097/346375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84639981/50000000000000 : ℝ)*(upper0) + (59473491/50000000000000 : ℝ)*(lower3) + (41214877/12500000000000 : ℝ)*(upper4) + (2182253679102031/50000000000000 : ℝ)*(major0) + (2182253679102031/50000000000000 : ℝ)*(major1) + (2182253679102031/50000000000000 : ℝ)*(major2) + (48466502133/50000000000000 : ℝ)*(sp1) + (42325452337/12500000000000 : ℝ)*(sp2) + (59434921531/50000000000000 : ℝ)*(sp3) + (1066006507/12500000000000 : ℝ)*(sp4) + (287144058358629/5000000000000 : ℝ)*(sp8) + (574279276222037/10000000000000 : ℝ)*(sp9) + (5742551091605939/100000000000000 : ℝ)*(sp10) + (295950971350387/10000000000000 : ℝ)*(sp11) + (739907145836733/25000000000000 : ℝ)*(f.failure) + (1148577939044927/20000000000000 : ℝ)*(f.sum) + (31922272667359/6927500000000000000000000000 : ℝ)*base65 + (472815260374521301/1385500000000000000000000000000000 : ℝ)*base68 + (16787693382360521301/1385500000000000000000000000000000 : ℝ)*base70 + (1648298274679521301/1385500000000000000000000000000000 : ℝ)*base72 + (35498880279857/3463750000000000000000000000 : ℝ)*base73 + (2516654849366521301/1385500000000000000000000000000000 : ℝ)*base76 + (5160949271343021301/1385500000000000000000000000000000 : ℝ)*base78 + (3789057244887978699/1385500000000000000000000000000000 : ℝ)*base79 + (29322491652603/3463750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (21472441/2500000000000000000000 : ℝ)*base89 + (21472441/2500000000000000000000 : ℝ)*base91 + (21472441/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82891/100000 : ℝ) ≤ (-143551733390920278559003832503161/173187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3231221/4000000000000 : ℝ)*(lower0) + (3910353/12500000000000 : ℝ)*(lower1) + (38231293/100000000000000 : ℝ)*(lower4) + (1099720460016103/25000000000000 : ℝ)*(major0) + (1099720460016103/25000000000000 : ℝ)*(major1) + (1099720460016103/25000000000000 : ℝ)*(major2) + (1240067783/25000000000000 : ℝ)*(sp0) + (304651713/250000000000 : ℝ)*(sp5) + (11548587311/50000000000000 : ℝ)*(sp6) + (13164935207/50000000000000 : ℝ)*(sp7) + (5842449706599139/100000000000000 : ℝ)*(sp12) + (5842332806185071/100000000000000 : ℝ)*(sp13) + (5842431569695649/100000000000000 : ℝ)*(sp14) + (1491456015904661/50000000000000 : ℝ)*(sp15) + (372867295209967/12500000000000 : ℝ)*(f.failure) + (5842454666870271/100000000000000 : ℝ)*(f.sum) + (39104135715063/13855000000000000000000000000 : ℝ)*base65 + (9275910666701984387/692750000000000000000000000000000 : ℝ)*base67 + (11400658509458984387/692750000000000000000000000000000 : ℝ)*base69 + (16260398985505234387/692750000000000000000000000000000 : ℝ)*base71 + (266573388628531/6927500000000000000000000000 : ℝ)*base74 + (10532667937457734387/692750000000000000000000000000000 : ℝ)*base75 + (14471457351314484387/692750000000000000000000000000000 : ℝ)*base77 + (40868816168922265613/692750000000000000000000000000000 : ℝ)*base80 + (6071237398691/1731875000000000000000000000 : ℝ)*base81 + (5276541/1250000000000000000000 : ℝ)*base90 + (5276541/1250000000000000000000 : ℝ)*base92 + (5276541/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1039_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59221/100000 : ℝ) else (79487/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82891/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1039_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1039_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59221/100000 : ℝ) else (79487/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82891/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1039_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1039_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59221/100000 : ℝ) else (79487/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82891/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

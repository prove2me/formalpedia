-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:08:11.829921+00:00
-- url     : https://prove2.me/submissions/a46bf24e-fdee-406b-94b4-4d70c76c21e5

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
theorem support_rectangle_w1068_s0_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1915454411/10000000000 : ℝ)*x 0 + (1517898083/2500000000 : ℝ)*x 1 + (4771042243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915454411/10000000000 : ℝ)^8261 ≤ (5554641909721/50000000000000 : ℝ)^6213 := by
    have hnat : (1915454411 : ℕ)^8261*50000000000000^6213 ≤ 5554641909721^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915454411 10000000000 5554641909721 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517898083/2500000000 : ℝ)^8261 ≤ (12876930227143/25000000000000 : ℝ)^6213 := by
    have hnat : (1517898083 : ℕ)^8261*25000000000000^6213 ≤ 12876930227143^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517898083 2500000000 12876930227143 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4771042243/10000000000 : ℝ)^8261 ≤ (18691497627373/50000000000000 : ℝ)^6213 := by
    have hnat : (4771042243 : ℕ)^8261*50000000000000^6213 ≤ 18691497627373^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771042243 10000000000 18691497627373 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1915454411/10000000000 : ℝ), (1517898083/2500000000 : ℝ), (4771042243/10000000000 : ℝ)] ![(5554641909721/50000000000000 : ℝ), (12876930227143/25000000000000 : ℝ), (18691497627373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1915454411/10000000000 : ℝ)|^8261 ≤ (5554641909721/50000000000000 : ℝ)^6213
        have hw : |(-1915454411/10000000000 : ℝ)|=(1915454411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1517898083/2500000000 : ℝ)|^8261 ≤ (12876930227143/25000000000000 : ℝ)^6213
        have hw : |(1517898083/2500000000 : ℝ)|=(1517898083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4771042243/10000000000 : ℝ)|^8261 ≤ (18691497627373/50000000000000 : ℝ)^6213
        have hw : |(4771042243/10000000000 : ℝ)|=(4771042243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520962097/10000000000 : ℝ)*x 0 + (-2663997391/10000000000 : ℝ)*x 1 + (74547521/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520962097/10000000000 : ℝ)^8261 ≤ (45391520104059/100000000000000 : ℝ)^6213 := by
    have hnat : (5520962097 : ℕ)^8261*100000000000000^6213 ≤ 45391520104059^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520962097 10000000000 45391520104059 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663997391/10000000000 : ℝ)^8261 ≤ (17225493993763/100000000000000 : ℝ)^6213 := by
    have hnat : (2663997391 : ℕ)^8261*100000000000000^6213 ≤ 17225493993763^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663997391 10000000000 17225493993763 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74547521/156250000 : ℝ)^8261 ≤ (37382985888797/100000000000000 : ℝ)^6213 := by
    have hnat : (74547521 : ℕ)^8261*100000000000000^6213 ≤ 37382985888797^6213*156250000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74547521 156250000 37382985888797 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520962097/10000000000 : ℝ), (-2663997391/10000000000 : ℝ), (74547521/156250000 : ℝ)] ![(45391520104059/100000000000000 : ℝ), (17225493993763/100000000000000 : ℝ), (37382985888797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520962097/10000000000 : ℝ)|^8261 ≤ (45391520104059/100000000000000 : ℝ)^6213
        have hw : |(5520962097/10000000000 : ℝ)|=(5520962097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2663997391/10000000000 : ℝ)|^8261 ≤ (17225493993763/100000000000000 : ℝ)^6213
        have hw : |(-2663997391/10000000000 : ℝ)|=(2663997391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74547521/156250000 : ℝ)|^8261 ≤ (37382985888797/100000000000000 : ℝ)^6213
        have hw : |(74547521/156250000 : ℝ)|=(74547521/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520958299/10000000000 : ℝ)*x 0 + (298190241/625000000 : ℝ)*x 1 + (-106559967/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520958299/10000000000 : ℝ)^8261 ≤ (4539147858513/10000000000000 : ℝ)^6213 := by
    have hnat : (5520958299 : ℕ)^8261*10000000000000^6213 ≤ 4539147858513^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520958299 10000000000 4539147858513 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298190241/625000000 : ℝ)^8261 ≤ (37383012059281/100000000000000 : ℝ)^6213 := by
    have hnat : (298190241 : ℕ)^8261*100000000000000^6213 ≤ 37383012059281^6213*625000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298190241 625000000 37383012059281 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106559967/400000000 : ℝ)^8261 ≤ (8612754665799/50000000000000 : ℝ)^6213 := by
    have hnat : (106559967 : ℕ)^8261*50000000000000^6213 ≤ 8612754665799^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106559967 400000000 8612754665799 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520958299/10000000000 : ℝ), (298190241/625000000 : ℝ), (-106559967/400000000 : ℝ)] ![(4539147858513/10000000000000 : ℝ), (37383012059281/100000000000000 : ℝ), (8612754665799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520958299/10000000000 : ℝ)|^8261 ≤ (4539147858513/10000000000000 : ℝ)^6213
        have hw : |(5520958299/10000000000 : ℝ)|=(5520958299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(298190241/625000000 : ℝ)|^8261 ≤ (37383012059281/100000000000000 : ℝ)^6213
        have hw : |(298190241/625000000 : ℝ)|=(298190241/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106559967/400000000 : ℝ)|^8261 ≤ (8612754665799/50000000000000 : ℝ)^6213
        have hw : |(-106559967/400000000 : ℝ)|=(106559967/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (65735061/156250000 : ℝ)*x 0 + (124990429/400000000 : ℝ)*x 1 + (1418666731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65735061/156250000 : ℝ)^8261 ≤ (1264992805429/4000000000000 : ℝ)^6213 := by
    have hnat : (65735061 : ℕ)^8261*4000000000000^6213 ≤ 1264992805429^6213*156250000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65735061 156250000 1264992805429 4000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124990429/400000000 : ℝ)^8261 ≤ (21295728533861/100000000000000 : ℝ)^6213 := by
    have hnat : (124990429 : ℕ)^8261*100000000000000^6213 ≤ 21295728533861^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124990429 400000000 21295728533861 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1418666731/2500000000 : ℝ)^8261 ≤ (47079451309077/100000000000000 : ℝ)^6213 := by
    have hnat : (1418666731 : ℕ)^8261*100000000000000^6213 ≤ 47079451309077^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418666731 2500000000 47079451309077 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65735061/156250000 : ℝ), (124990429/400000000 : ℝ), (1418666731/2500000000 : ℝ)] ![(1264992805429/4000000000000 : ℝ), (21295728533861/100000000000000 : ℝ), (47079451309077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65735061/156250000 : ℝ)|^8261 ≤ (1264992805429/4000000000000 : ℝ)^6213
        have hw : |(65735061/156250000 : ℝ)|=(65735061/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124990429/400000000 : ℝ)|^8261 ≤ (21295728533861/100000000000000 : ℝ)^6213
        have hw : |(124990429/400000000 : ℝ)|=(124990429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1418666731/2500000000 : ℝ)|^8261 ≤ (47079451309077/100000000000000 : ℝ)^6213
        have hw : |(1418666731/2500000000 : ℝ)|=(1418666731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-24010269/125000000 : ℝ)*x 0 + (4804622823/10000000000 : ℝ)*x 1 + (6036837033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24010269/125000000 : ℝ)^8261 ≤ (11150692016163/100000000000000 : ℝ)^6213 := by
    have hnat : (24010269 : ℕ)^8261*100000000000000^6213 ≤ 11150692016163^6213*125000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24010269 125000000 11150692016163 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4804622823/10000000000 : ℝ)^8261 ≤ (2358328073887/6250000000000 : ℝ)^6213 := by
    have hnat : (4804622823 : ℕ)^8261*6250000000000^6213 ≤ 2358328073887^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804622823 10000000000 2358328073887 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6036837033/10000000000 : ℝ)^8261 ≤ (51116058784339/100000000000000 : ℝ)^6213 := by
    have hnat : (6036837033 : ℕ)^8261*100000000000000^6213 ≤ 51116058784339^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036837033 10000000000 51116058784339 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24010269/125000000 : ℝ), (4804622823/10000000000 : ℝ), (6036837033/10000000000 : ℝ)] ![(11150692016163/100000000000000 : ℝ), (2358328073887/6250000000000 : ℝ), (51116058784339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24010269/125000000 : ℝ)|^8261 ≤ (11150692016163/100000000000000 : ℝ)^6213
        have hw : |(-24010269/125000000 : ℝ)|=(24010269/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4804622823/10000000000 : ℝ)|^8261 ≤ (2358328073887/6250000000000 : ℝ)^6213
        have hw : |(4804622823/10000000000 : ℝ)|=(4804622823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6036837033/10000000000 : ℝ)|^8261 ≤ (51116058784339/100000000000000 : ℝ)^6213
        have hw : |(6036837033/10000000000 : ℝ)|=(6036837033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1291989949/2500000000 : ℝ)*x 0 + (-43693973/312500000 : ℝ)*x 1 + (1509208719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291989949/2500000000 : ℝ)^8261 ≤ (41573836481239/100000000000000 : ℝ)^6213 := by
    have hnat : (1291989949 : ℕ)^8261*100000000000000^6213 ≤ 41573836481239^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291989949 2500000000 41573836481239 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43693973/312500000 : ℝ)^8261 ≤ (7310129001193/100000000000000 : ℝ)^6213 := by
    have hnat : (43693973 : ℕ)^8261*100000000000000^6213 ≤ 7310129001193^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43693973 312500000 7310129001193 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1509208719/2500000000 : ℝ)^8261 ≤ (51116034499831/100000000000000 : ℝ)^6213 := by
    have hnat : (1509208719 : ℕ)^8261*100000000000000^6213 ≤ 51116034499831^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509208719 2500000000 51116034499831 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291989949/2500000000 : ℝ), (-43693973/312500000 : ℝ), (1509208719/2500000000 : ℝ)] ![(41573836481239/100000000000000 : ℝ), (7310129001193/100000000000000 : ℝ), (51116034499831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291989949/2500000000 : ℝ)|^8261 ≤ (41573836481239/100000000000000 : ℝ)^6213
        have hw : |(1291989949/2500000000 : ℝ)|=(1291989949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43693973/312500000 : ℝ)|^8261 ≤ (7310129001193/100000000000000 : ℝ)^6213
        have hw : |(-43693973/312500000 : ℝ)|=(43693973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1509208719/2500000000 : ℝ)|^8261 ≤ (51116034499831/100000000000000 : ℝ)^6213
        have hw : |(1509208719/2500000000 : ℝ)|=(1509208719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583979937/5000000000 : ℝ)*x 0 + (6036836173/10000000000 : ℝ)*x 1 + (-349551229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583979937/5000000000 : ℝ)^8261 ≤ (10393459328887/25000000000000 : ℝ)^6213 := by
    have hnat : (2583979937 : ℕ)^8261*25000000000000^6213 ≤ 10393459328887^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583979937 5000000000 10393459328887 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036836173/10000000000 : ℝ)^8261 ≤ (51116049102059/100000000000000 : ℝ)^6213 := by
    have hnat : (6036836173 : ℕ)^8261*100000000000000^6213 ≤ 51116049102059^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036836173 10000000000 51116049102059 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349551229/2500000000 : ℝ)^8261 ≤ (1827528392161/25000000000000 : ℝ)^6213 := by
    have hnat : (349551229 : ℕ)^8261*25000000000000^6213 ≤ 1827528392161^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349551229 2500000000 1827528392161 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583979937/5000000000 : ℝ), (6036836173/10000000000 : ℝ), (-349551229/2500000000 : ℝ)] ![(10393459328887/25000000000000 : ℝ), (51116049102059/100000000000000 : ℝ), (1827528392161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583979937/5000000000 : ℝ)|^8261 ≤ (10393459328887/25000000000000 : ℝ)^6213
        have hw : |(2583979937/5000000000 : ℝ)|=(2583979937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036836173/10000000000 : ℝ)|^8261 ≤ (51116049102059/100000000000000 : ℝ)^6213
        have hw : |(6036836173/10000000000 : ℝ)|=(6036836173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349551229/2500000000 : ℝ)|^8261 ≤ (1827528392161/25000000000000 : ℝ)^6213
        have hw : |(-349551229/2500000000 : ℝ)|=(349551229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s0_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (131798939/312500000 : ℝ)*x 0 + (5608826141/10000000000 : ℝ)*x 1 + (159645193/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131798939/312500000 : ℝ)^8261 ≤ (15865016084809/50000000000000 : ℝ)^6213 := by
    have hnat : (131798939 : ℕ)^8261*50000000000000^6213 ≤ 15865016084809^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131798939 312500000 15865016084809 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608826141/10000000000 : ℝ)^8261 ≤ (4635454177153/10000000000000 : ℝ)^6213 := by
    have hnat : (5608826141 : ℕ)^8261*10000000000000^6213 ≤ 4635454177153^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608826141 10000000000 4635454177153 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159645193/500000000 : ℝ)^8261 ≤ (10957713021751/50000000000000 : ℝ)^6213 := by
    have hnat : (159645193 : ℕ)^8261*50000000000000^6213 ≤ 10957713021751^6213*500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159645193 500000000 10957713021751 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131798939/312500000 : ℝ), (5608826141/10000000000 : ℝ), (159645193/500000000 : ℝ)] ![(15865016084809/50000000000000 : ℝ), (4635454177153/10000000000000 : ℝ), (10957713021751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131798939/312500000 : ℝ)|^8261 ≤ (15865016084809/50000000000000 : ℝ)^6213
        have hw : |(131798939/312500000 : ℝ)|=(131798939/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608826141/10000000000 : ℝ)|^8261 ≤ (4635454177153/10000000000000 : ℝ)^6213
        have hw : |(5608826141/10000000000 : ℝ)|=(5608826141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159645193/500000000 : ℝ)|^8261 ≤ (10957713021751/50000000000000 : ℝ)^6213
        have hw : |(159645193/500000000 : ℝ)|=(159645193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (21/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28101/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2065/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2065 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2065*1^512 ≤ 0^512*1^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2065/512 : ℝ) ≤ (62082203368675609/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2065 ≤ (62082203368675609/2500000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2065*2500000000000000000^512 ≤ 62082203368675609^512*5^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 62082203368675609 2500000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (62082203368675609/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2065 := by
      have hnat : (1 : ℕ)^512*1^2065 ≤ 1^2065*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2562082203368675609/2500000000000000000 : ℝ) ≤ (503050218475533/500000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (2562082203368675609/2500000000000000000 : ℝ)^512 ≤ (503050218475533/500000000000000 : ℝ)^2065 := by
      have hnat : (2562082203368675609 : ℕ)^512*500000000000000^2065 ≤ 503050218475533^2065*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2562082203368675609 2500000000000000000 503050218475533 500000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (503050218475533/500000000000000 : ℝ)) (X := (2562082203368675609/2500000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1312082203368675609/1250000000000000000 : ℝ) ≤ (253050218475533/250000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (1312082203368675609/1250000000000000000 : ℝ)^512 ≤ (253050218475533/250000000000000 : ℝ)^2065 := by
      have hnat : (1312082203368675609 : ℕ)^512*250000000000000^2065 ≤ 253050218475533^2065*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1312082203368675609 1250000000000000000 253050218475533 250000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (253050218475533/250000000000000 : ℝ)) (X := (1312082203368675609/1250000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3050218475533/200000000000000 : ℝ)*(0 : ℝ))^(2065/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3050218475533/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(62082203368675609/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3050218475533/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (1 : ℝ)+(3050218475533/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(503050218475533/500000000000000 : ℝ) by norm_num, show 1+(62082203368675609/2500000000000000000 : ℝ)+(0 : ℝ)=(2562082203368675609/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(62082203368675609/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3050218475533/200000000000000 : ℝ)*(2/5 : ℝ))^(2065/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3050218475533/200000000000000 : ℝ)*(2/5 : ℝ)=(253050218475533/250000000000000 : ℝ) by norm_num, show 1+2*(62082203368675609/2500000000000000000 : ℝ)=(1312082203368675609/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3050218475533/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3050218475533/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3050218475533/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3050218475533/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3050218475533/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3050218475533/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1915454411/10000000000 : ℝ)*X 0 0+(1517898083/2500000000 : ℝ)*X 0 1+(4771042243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520962097/10000000000 : ℝ)*X 1 0+(-2663997391/10000000000 : ℝ)*X 1 1+(74547521/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5520958299/10000000000 : ℝ)*X 2 0+(298190241/625000000 : ℝ)*X 2 1+(-106559967/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65735061/156250000 : ℝ)*X 0 0+(124990429/400000000 : ℝ)*X 0 1+(1418666731/2500000000 : ℝ)*X 0 2+(65735061/156250000 : ℝ)*X 1 0+(124990429/400000000 : ℝ)*X 1 1+(1418666731/2500000000 : ℝ)*X 1 2+(65735061/156250000 : ℝ)*X 2 0+(124990429/400000000 : ℝ)*X 2 1+(1418666731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-24010269/125000000 : ℝ)*X 0 0+(4804622823/10000000000 : ℝ)*X 0 1+(6036837033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1291989949/2500000000 : ℝ)*X 1 0+(-43693973/312500000 : ℝ)*X 1 1+(1509208719/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583979937/5000000000 : ℝ)*X 2 0+(6036836173/10000000000 : ℝ)*X 2 1+(-349551229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((131798939/312500000 : ℝ)*X 0 0+(5608826141/10000000000 : ℝ)*X 0 1+(159645193/500000000 : ℝ)*X 0 2+(131798939/312500000 : ℝ)*X 1 0+(5608826141/10000000000 : ℝ)*X 1 1+(159645193/500000000 : ℝ)*X 1 2+(131798939/312500000 : ℝ)*X 2 0+(5608826141/10000000000 : ℝ)*X 2 1+(159645193/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139637522866277319/31250000000000000000000 : ℝ) := by norm_num
    linear_combination (5760091/25000000000000 : ℝ)*(base1) + (51499547/50000000000000 : ℝ)*(base16) + (146035757/12500000000000 : ℝ)*(base19) + (742333687/100000000000000 : ℝ)*(base23) + (259207021/100000000000000 : ℝ)*(upper3) + (580542419943373/100000000000000 : ℝ)*(major0) + (580542419943373/100000000000000 : ℝ)*(major1) + (580542419943373/100000000000000 : ℝ)*(major2) + (768909218804569/100000000000000 : ℝ)*(sp0) + (768909681682399/100000000000000 : ℝ)*(sp1) + (384455105316931/50000000000000 : ℝ)*(sp2) + (392172299661681/100000000000000 : ℝ)*(sp3) + (1757203343/100000000000000 : ℝ)*(sp4) + (1415270457/100000000000000 : ℝ)*(sp7) + (196086868986251/50000000000000 : ℝ)*(f.failure) + (768910952967549/100000000000000 : ℝ)*(f.sum) + (10169167417191/10000000000000000000000000000 : ℝ)*base66 + (90697098812809/20000000000000000000000000000 : ℝ)*base67 + (176799988992809/20000000000000000000000000000 : ℝ)*base69 + (22585900732809/20000000000000000000000000000 : ℝ)*base71 + (45674495537191/10000000000000000000000000000 : ℝ)*base74 + (41437904407191/20000000000000000000000000000 : ℝ)*base76 + (54820100032809/20000000000000000000000000000 : ℝ)*base77 + (16982694687191/20000000000000000000000000000 : ℝ)*base80 + (33236851852809/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1760697/5000000000000000000000 : ℝ)*base89 + (1760697/5000000000000000000000 : ℝ)*base91 + (1760697/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30018229329335377726287/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231616631/50000000000000 : ℝ)*(base19) + (664073573/100000000000000 : ℝ)*(base23) + (147147347/100000000000000 : ℝ)*(base39) + (853617/10000000000000 : ℝ)*(upper3) + (122822211/50000000000000 : ℝ)*(upper5) + (612733981260487/100000000000000 : ℝ)*(major0) + (612733981260487/100000000000000 : ℝ)*(major1) + (30636691705657/5000000000000 : ℝ)*(major2) + (67032589/10000000000000 : ℝ)*(sp2) + (7779489/25000000000000 : ℝ)*(sp3) + (101443452065583/12500000000000 : ℝ)*(sp4) + (811547153291401/100000000000000 : ℝ)*(sp5) + (202886607318137/25000000000000 : ℝ)*(sp6) + (206960033835119/50000000000000 : ℝ)*(sp7) + (206960049394097/50000000000000 : ℝ)*(f.failure) + (81154776367201/10000000000000 : ℝ)*(f.sum) + (38015745608191/20000000000000000000000000000 : ℝ)*base65 + (5609883939819/1000000000000000000000000000 : ℝ)*base68 + (94874849555429/20000000000000000000000000000 : ℝ)*base70 + (1184041653819/1000000000000000000000000000 : ℝ)*base72 + (23498110528191/20000000000000000000000000000 : ℝ)*base73 + (38032763164571/20000000000000000000000000000 : ℝ)*base75 + (128501485035429/20000000000000000000000000000 : ℝ)*base78 + (160706696875429/20000000000000000000000000000 : ℝ)*base80 + (39302716104571/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (783141/5000000000000000000000 : ℝ)*base90 + (783141/5000000000000000000000 : ℝ)*base92 + (783141/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1068_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1068_s1_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-531361833/2500000000 : ℝ)*x 0 + (2860875129/5000000000 : ℝ)*x 1 + (4986404933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531361833/2500000000 : ℝ)^8261 ≤ (12757243709217/100000000000000 : ℝ)^6213 := by
    have hnat : (531361833 : ℕ)^8261*100000000000000^6213 ≤ 12757243709217^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531361833 2500000000 12757243709217 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2860875129/5000000000 : ℝ)^8261 ≤ (743742896269/1562500000000 : ℝ)^6213 := by
    have hnat : (2860875129 : ℕ)^8261*1562500000000^6213 ≤ 743742896269^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860875129 5000000000 743742896269 1562500000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986404933/10000000000 : ℝ)^8261 ≤ (4955401363249/12500000000000 : ℝ)^6213 := by
    have hnat : (4986404933 : ℕ)^8261*12500000000000^6213 ≤ 4955401363249^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986404933 10000000000 4955401363249 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531361833/2500000000 : ℝ), (2860875129/5000000000 : ℝ), (4986404933/10000000000 : ℝ)] ![(12757243709217/100000000000000 : ℝ), (743742896269/1562500000000 : ℝ), (4955401363249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531361833/2500000000 : ℝ)|^8261 ≤ (12757243709217/100000000000000 : ℝ)^6213
        have hw : |(-531361833/2500000000 : ℝ)|=(531361833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2860875129/5000000000 : ℝ)|^8261 ≤ (743742896269/1562500000000 : ℝ)^6213
        have hw : |(2860875129/5000000000 : ℝ)|=(2860875129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986404933/10000000000 : ℝ)|^8261 ≤ (4955401363249/12500000000000 : ℝ)^6213
        have hw : |(4986404933/10000000000 : ℝ)|=(4986404933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355799831/2500000000 : ℝ)*x 0 + (-10095257/40000000 : ℝ)*x 1 + (38956291/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355799831/2500000000 : ℝ)^8261 ≤ (221629648029/500000000000 : ℝ)^6213 := by
    have hnat : (1355799831 : ℕ)^8261*500000000000^6213 ≤ 221629648029^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355799831 2500000000 221629648029 500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10095257/40000000 : ℝ)^8261 ≤ (80154280759/500000000000 : ℝ)^6213 := by
    have hnat : (10095257 : ℕ)^8261*500000000000^6213 ≤ 80154280759^6213*40000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10095257 40000000 80154280759 500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38956291/78125000 : ℝ)^8261 ≤ (3964321423583/10000000000000 : ℝ)^6213 := by
    have hnat : (38956291 : ℕ)^8261*10000000000000^6213 ≤ 3964321423583^6213*78125000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38956291 78125000 3964321423583 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355799831/2500000000 : ℝ), (-10095257/40000000 : ℝ), (38956291/78125000 : ℝ)] ![(221629648029/500000000000 : ℝ), (80154280759/500000000000 : ℝ), (3964321423583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355799831/2500000000 : ℝ)|^8261 ≤ (221629648029/500000000000 : ℝ)^6213
        have hw : |(1355799831/2500000000 : ℝ)|=(1355799831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10095257/40000000 : ℝ)|^8261 ≤ (80154280759/500000000000 : ℝ)^6213
        have hw : |(-10095257/40000000 : ℝ)|=(10095257/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(38956291/78125000 : ℝ)|^8261 ≤ (3964321423583/10000000000000 : ℝ)^6213
        have hw : |(38956291/78125000 : ℝ)|=(38956291/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67789999/125000000 : ℝ)*x 0 + (155825143/312500000 : ℝ)*x 1 + (-2523814323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67789999/125000000 : ℝ)^8261 ≤ (5540742010361/12500000000000 : ℝ)^6213 := by
    have hnat : (67789999 : ℕ)^8261*12500000000000^6213 ≤ 5540742010361^6213*125000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67789999 125000000 5540742010361 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155825143/312500000 : ℝ)^8261 ≤ (2477700445761/6250000000000 : ℝ)^6213 := by
    have hnat : (155825143 : ℕ)^8261*6250000000000^6213 ≤ 2477700445761^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155825143 312500000 2477700445761 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2523814323/10000000000 : ℝ)^8261 ≤ (16030856768329/100000000000000 : ℝ)^6213 := by
    have hnat : (2523814323 : ℕ)^8261*100000000000000^6213 ≤ 16030856768329^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2523814323 10000000000 16030856768329 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67789999/125000000 : ℝ), (155825143/312500000 : ℝ), (-2523814323/10000000000 : ℝ)] ![(5540742010361/12500000000000 : ℝ), (2477700445761/6250000000000 : ℝ), (16030856768329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67789999/125000000 : ℝ)|^8261 ≤ (5540742010361/12500000000000 : ℝ)^6213
        have hw : |(67789999/125000000 : ℝ)|=(67789999/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155825143/312500000 : ℝ)|^8261 ≤ (2477700445761/6250000000000 : ℝ)^6213
        have hw : |(155825143/312500000 : ℝ)|=(155825143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2523814323/10000000000 : ℝ)|^8261 ≤ (16030856768329/100000000000000 : ℝ)^6213
        have hw : |(-2523814323/10000000000 : ℝ)|=(2523814323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (135113733/312500000 : ℝ)*x 0 + (1831473419/5000000000 : ℝ)*x 1 + (127617303/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135113733/312500000 : ℝ)^8261 ≤ (32795481858571/100000000000000 : ℝ)^6213 := by
    have hnat : (135113733 : ℕ)^8261*100000000000000^6213 ≤ 32795481858571^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135113733 312500000 32795481858571 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831473419/5000000000 : ℝ)^8261 ≤ (5261208082147/20000000000000 : ℝ)^6213 := by
    have hnat : (1831473419 : ℕ)^8261*20000000000000^6213 ≤ 5261208082147^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831473419 5000000000 5261208082147 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127617303/250000000 : ℝ)^8261 ≤ (2044923885679/5000000000000 : ℝ)^6213 := by
    have hnat : (127617303 : ℕ)^8261*5000000000000^6213 ≤ 2044923885679^6213*250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127617303 250000000 2044923885679 5000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135113733/312500000 : ℝ), (1831473419/5000000000 : ℝ), (127617303/250000000 : ℝ)] ![(32795481858571/100000000000000 : ℝ), (5261208082147/20000000000000 : ℝ), (2044923885679/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135113733/312500000 : ℝ)|^8261 ≤ (32795481858571/100000000000000 : ℝ)^6213
        have hw : |(135113733/312500000 : ℝ)|=(135113733/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1831473419/5000000000 : ℝ)|^8261 ≤ (5261208082147/20000000000000 : ℝ)^6213
        have hw : |(1831473419/5000000000 : ℝ)|=(1831473419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127617303/250000000 : ℝ)|^8261 ≤ (2044923885679/5000000000000 : ℝ)^6213
        have hw : |(127617303/250000000 : ℝ)|=(127617303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85054651/400000000 : ℝ)*x 0 + (312295691/625000000 : ℝ)*x 1 + (5711212281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85054651/400000000 : ℝ)^8261 ≤ (3191144496477/25000000000000 : ℝ)^6213 := by
    have hnat : (85054651 : ℕ)^8261*25000000000000^6213 ≤ 3191144496477^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85054651 400000000 3191144496477 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312295691/625000000 : ℝ)^8261 ≤ (4969050588153/12500000000000 : ℝ)^6213 := by
    have hnat : (312295691 : ℕ)^8261*12500000000000^6213 ≤ 4969050588153^6213*625000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312295691 625000000 4969050588153 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5711212281/10000000000 : ℝ)^8261 ≤ (11870754325167/25000000000000 : ℝ)^6213 := by
    have hnat : (5711212281 : ℕ)^8261*25000000000000^6213 ≤ 11870754325167^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711212281 10000000000 11870754325167 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85054651/400000000 : ℝ), (312295691/625000000 : ℝ), (5711212281/10000000000 : ℝ)] ![(3191144496477/25000000000000 : ℝ), (4969050588153/12500000000000 : ℝ), (11870754325167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85054651/400000000 : ℝ)|^8261 ≤ (3191144496477/25000000000000 : ℝ)^6213
        have hw : |(-85054651/400000000 : ℝ)|=(85054651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312295691/625000000 : ℝ)|^8261 ≤ (4969050588153/12500000000000 : ℝ)^6213
        have hw : |(312295691/625000000 : ℝ)|=(312295691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5711212281/10000000000 : ℝ)|^8261 ≤ (11870754325167/25000000000000 : ℝ)^6213
        have hw : |(5711212281/10000000000 : ℝ)|=(5711212281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1308845989/2500000000 : ℝ)*x 0 + (-449751237/2500000000 : ℝ)*x 1 + (2855607027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308845989/2500000000 : ℝ)^8261 ≤ (42296569573323/100000000000000 : ℝ)^6213 := by
    have hnat : (1308845989 : ℕ)^8261*100000000000000^6213 ≤ 42296569573323^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308845989 2500000000 42296569573323 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449751237/2500000000 : ℝ)^8261 ≤ (1277549188967/12500000000000 : ℝ)^6213 := by
    have hnat : (449751237 : ℕ)^8261*12500000000000^6213 ≤ 1277549188967^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449751237 2500000000 1277549188967 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855607027/5000000000 : ℝ)^8261 ≤ (11870759225099/25000000000000 : ℝ)^6213 := by
    have hnat : (2855607027 : ℕ)^8261*25000000000000^6213 ≤ 11870759225099^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855607027 5000000000 11870759225099 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308845989/2500000000 : ℝ), (-449751237/2500000000 : ℝ), (2855607027/5000000000 : ℝ)] ![(42296569573323/100000000000000 : ℝ), (1277549188967/12500000000000 : ℝ), (11870759225099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308845989/2500000000 : ℝ)|^8261 ≤ (42296569573323/100000000000000 : ℝ)^6213
        have hw : |(1308845989/2500000000 : ℝ)|=(1308845989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449751237/2500000000 : ℝ)|^8261 ≤ (1277549188967/12500000000000 : ℝ)^6213
        have hw : |(-449751237/2500000000 : ℝ)|=(449751237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2855607027/5000000000 : ℝ)|^8261 ≤ (11870759225099/25000000000000 : ℝ)^6213
        have hw : |(2855607027/5000000000 : ℝ)|=(2855607027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5235381913/10000000000 : ℝ)*x 0 + (5711216313/10000000000 : ℝ)*x 1 + (-1799004547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235381913/10000000000 : ℝ)^8261 ≤ (42296547627281/100000000000000 : ℝ)^6213 := by
    have hnat : (5235381913 : ℕ)^8261*100000000000000^6213 ≤ 42296547627281^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235381913 10000000000 42296547627281 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5711216313/10000000000 : ℝ)^8261 ≤ (4637017761/9765625000 : ℝ)^6213 := by
    have hnat : (5711216313 : ℕ)^8261*9765625000^6213 ≤ 4637017761^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711216313 10000000000 4637017761 9765625000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799004547/10000000000 : ℝ)^8261 ≤ (2044078096531/20000000000000 : ℝ)^6213 := by
    have hnat : (1799004547 : ℕ)^8261*20000000000000^6213 ≤ 2044078096531^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799004547 10000000000 2044078096531 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235381913/10000000000 : ℝ), (5711216313/10000000000 : ℝ), (-1799004547/10000000000 : ℝ)] ![(42296547627281/100000000000000 : ℝ), (4637017761/9765625000 : ℝ), (2044078096531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235381913/10000000000 : ℝ)|^8261 ≤ (42296547627281/100000000000000 : ℝ)^6213
        have hw : |(5235381913/10000000000 : ℝ)|=(5235381913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5711216313/10000000000 : ℝ)|^8261 ≤ (4637017761/9765625000 : ℝ)^6213
        have hw : |(5711216313/10000000000 : ℝ)|=(5711216313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1799004547/10000000000 : ℝ)|^8261 ≤ (2044078096531/20000000000000 : ℝ)^6213
        have hw : |(-1799004547/10000000000 : ℝ)|=(1799004547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (270339817/625000000 : ℝ)*x 0 + (1016888577/2000000000 : ℝ)*x 1 + (3683604401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270339817/625000000 : ℝ)^8261 ≤ (820340322233/2500000000000 : ℝ)^6213 := by
    have hnat : (270339817 : ℕ)^8261*2500000000000^6213 ≤ 820340322233^6213*625000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270339817 625000000 820340322233 2500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016888577/2000000000 : ℝ)^8261 ≤ (20341452646859/50000000000000 : ℝ)^6213 := by
    have hnat : (1016888577 : ℕ)^8261*50000000000000^6213 ≤ 20341452646859^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016888577 2000000000 20341452646859 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3683604401/10000000000 : ℝ)^8261 ≤ (26503481801643/100000000000000 : ℝ)^6213 := by
    have hnat : (3683604401 : ℕ)^8261*100000000000000^6213 ≤ 26503481801643^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683604401 10000000000 26503481801643 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270339817/625000000 : ℝ), (1016888577/2000000000 : ℝ), (3683604401/10000000000 : ℝ)] ![(820340322233/2500000000000 : ℝ), (20341452646859/50000000000000 : ℝ), (26503481801643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270339817/625000000 : ℝ)|^8261 ≤ (820340322233/2500000000000 : ℝ)^6213
        have hw : |(270339817/625000000 : ℝ)|=(270339817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016888577/2000000000 : ℝ)|^8261 ≤ (20341452646859/50000000000000 : ℝ)^6213
        have hw : |(1016888577/2000000000 : ℝ)|=(1016888577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3683604401/10000000000 : ℝ)|^8261 ≤ (26503481801643/100000000000000 : ℝ)^6213
        have hw : |(3683604401/10000000000 : ℝ)|=(3683604401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_8 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8641757/10000000000 : ℝ)*x 0 + (686231649/1250000000 : ℝ)*x 1 + (796676697/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8641757/10000000000 : ℝ)^8261 ≤ (66008501/781250000000 : ℝ)^6213 := by
    have hnat : (8641757 : ℕ)^8261*781250000000^6213 ≤ 66008501^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8641757 10000000000 66008501 781250000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686231649/1250000000 : ℝ)^8261 ≤ (11262940087267/25000000000000 : ℝ)^6213 := by
    have hnat : (686231649 : ℕ)^8261*25000000000000^6213 ≤ 11262940087267^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686231649 1250000000 11262940087267 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796676697/1250000000 : ℝ)^8261 ≤ (54939790550779/100000000000000 : ℝ)^6213 := by
    have hnat : (796676697 : ℕ)^8261*100000000000000^6213 ≤ 54939790550779^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796676697 1250000000 54939790550779 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8641757/10000000000 : ℝ), (686231649/1250000000 : ℝ), (796676697/1250000000 : ℝ)] ![(66008501/781250000000 : ℝ), (11262940087267/25000000000000 : ℝ), (54939790550779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8641757/10000000000 : ℝ)|^8261 ≤ (66008501/781250000000 : ℝ)^6213
        have hw : |(8641757/10000000000 : ℝ)|=(8641757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686231649/1250000000 : ℝ)|^8261 ≤ (11262940087267/25000000000000 : ℝ)^6213
        have hw : |(686231649/1250000000 : ℝ)|=(686231649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796676697/1250000000 : ℝ)|^8261 ≤ (54939790550779/100000000000000 : ℝ)^6213
        have hw : |(796676697/1250000000 : ℝ)|=(796676697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_9 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (482176569/5000000000 : ℝ)*x 0 + (-4457679629/10000000000 : ℝ)*x 1 + (6927944261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482176569/5000000000 : ℝ)^8261 ≤ (2230377662803/50000000000000 : ℝ)^6213 := by
    have hnat : (482176569 : ℕ)^8261*50000000000000^6213 ≤ 2230377662803^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482176569 5000000000 2230377662803 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4457679629/10000000000 : ℝ)^8261 ≤ (17077099571391/50000000000000 : ℝ)^6213 := by
    have hnat : (4457679629 : ℕ)^8261*50000000000000^6213 ≤ 17077099571391^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4457679629 10000000000 17077099571391 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6927944261/10000000000 : ℝ)^8261 ≤ (61385045524783/100000000000000 : ℝ)^6213 := by
    have hnat : (6927944261 : ℕ)^8261*100000000000000^6213 ≤ 61385045524783^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6927944261 10000000000 61385045524783 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482176569/5000000000 : ℝ), (-4457679629/10000000000 : ℝ), (6927944261/10000000000 : ℝ)] ![(2230377662803/50000000000000 : ℝ), (17077099571391/50000000000000 : ℝ), (61385045524783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482176569/5000000000 : ℝ)|^8261 ≤ (2230377662803/50000000000000 : ℝ)^6213
        have hw : |(482176569/5000000000 : ℝ)|=(482176569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4457679629/10000000000 : ℝ)|^8261 ≤ (17077099571391/50000000000000 : ℝ)^6213
        have hw : |(-4457679629/10000000000 : ℝ)|=(4457679629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6927944261/10000000000 : ℝ)|^8261 ≤ (61385045524783/100000000000000 : ℝ)^6213
        have hw : |(6927944261/10000000000 : ℝ)|=(6927944261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_10 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (964346949/10000000000 : ℝ)*x 0 + (692793089/1000000000 : ℝ)*x 1 + (-4457698827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964346949/10000000000 : ℝ)^8261 ≤ (2230358630401/50000000000000 : ℝ)^6213 := by
    have hnat : (964346949 : ℕ)^8261*50000000000000^6213 ≤ 2230358630401^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964346949 10000000000 2230358630401 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692793089/1000000000 : ℝ)^8261 ≤ (61384887998431/100000000000000 : ℝ)^6213 := by
    have hnat : (692793089 : ℕ)^8261*100000000000000^6213 ≤ 61384887998431^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692793089 1000000000 61384887998431 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4457698827/10000000000 : ℝ)^8261 ≤ (34154394722051/100000000000000 : ℝ)^6213 := by
    have hnat : (4457698827 : ℕ)^8261*100000000000000^6213 ≤ 34154394722051^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4457698827 10000000000 34154394722051 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(964346949/10000000000 : ℝ), (692793089/1000000000 : ℝ), (-4457698827/10000000000 : ℝ)] ![(2230358630401/50000000000000 : ℝ), (61384887998431/100000000000000 : ℝ), (34154394722051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(964346949/10000000000 : ℝ)|^8261 ≤ (2230358630401/50000000000000 : ℝ)^6213
        have hw : |(964346949/10000000000 : ℝ)|=(964346949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692793089/1000000000 : ℝ)|^8261 ≤ (61384887998431/100000000000000 : ℝ)^6213
        have hw : |(692793089/1000000000 : ℝ)|=(692793089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4457698827/10000000000 : ℝ)|^8261 ≤ (34154394722051/100000000000000 : ℝ)^6213
        have hw : |(-4457698827/10000000000 : ℝ)|=(4457698827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s1_11 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1924833357/10000000000 : ℝ)*x 0 + (1166000497/2000000000 : ℝ)*x 1 + (2510893099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924833357/10000000000 : ℝ)^8261 ≤ (11181668973659/100000000000000 : ℝ)^6213 := by
    have hnat : (1924833357 : ℕ)^8261*100000000000000^6213 ≤ 11181668973659^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924833357 10000000000 11181668973659 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166000497/2000000000 : ℝ)^8261 ≤ (48800671090761/100000000000000 : ℝ)^6213 := by
    have hnat : (1166000497 : ℕ)^8261*100000000000000^6213 ≤ 48800671090761^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166000497 2000000000 48800671090761 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510893099/5000000000 : ℝ)^8261 ≤ (5002207490343/12500000000000 : ℝ)^6213 := by
    have hnat : (2510893099 : ℕ)^8261*12500000000000^6213 ≤ 5002207490343^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510893099 5000000000 5002207490343 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1924833357/10000000000 : ℝ), (1166000497/2000000000 : ℝ), (2510893099/5000000000 : ℝ)] ![(11181668973659/100000000000000 : ℝ), (48800671090761/100000000000000 : ℝ), (5002207490343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1924833357/10000000000 : ℝ)|^8261 ≤ (11181668973659/100000000000000 : ℝ)^6213
        have hw : |(1924833357/10000000000 : ℝ)|=(1924833357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1166000497/2000000000 : ℝ)|^8261 ≤ (48800671090761/100000000000000 : ℝ)^6213
        have hw : |(1166000497/2000000000 : ℝ)|=(1166000497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510893099/5000000000 : ℝ)|^8261 ≤ (5002207490343/12500000000000 : ℝ)^6213
        have hw : |(2510893099/5000000000 : ℝ)|=(2510893099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (209/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (21/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (21/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (21/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (21/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (21/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (21/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (21/20000 : ℝ) ^ (2065/512 : ℝ) ≤ (19358931/20000000000000000000 : ℝ) := by
    have hpowers : (21/20000 : ℝ)^2065 ≤ (19358931/20000000000000000000 : ℝ)^512 := by
      have hnat : (21 : ℕ)^2065*20000000000000000000^512 ≤ 19358931^512*20000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21 20000 19358931 20000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21/20000 : ℝ)) (X := (19358931/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (28101/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (597837206565561553/100000000000000000000 : ℝ) := by
    have hpowers : (28101/100000 : ℝ)^2065 ≤ (597837206565561553/100000000000000000000 : ℝ)^512 := by
      have hnat : (28101 : ℕ)^2065*100000000000000000000^512 ≤ 597837206565561553^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28101 100000 597837206565561553 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28101/100000 : ℝ)) (X := (597837206565561553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000019358931/10000000000000000000 : ℝ) ≤ (6250000000003/6250000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (10000000000019358931/10000000000000000000 : ℝ)^512 ≤ (6250000000003/6250000000000 : ℝ)^2065 := by
      have hnat : (10000000000019358931 : ℕ)^512*6250000000000^2065 ≤ 6250000000003^2065*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000019358931 10000000000000000000 6250000000003 6250000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6250000000003/6250000000000 : ℝ)) (X := (10000000000019358931/10000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6287364825416397263/6250000000000000000 : ℝ) ≤ (10014789682008933/10000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (6287364825416397263/6250000000000000000 : ℝ)^512 ≤ (10014789682008933/10000000000000000 : ℝ)^2065 := by
      have hnat : (6287364825416397263 : ℕ)^512*10000000000000000^2065 ≤ 10014789682008933^2065*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6287364825416397263 6250000000000000000 10014789682008933 10000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014789682008933/10000000000000000 : ℝ)) (X := (6287364825416397263/6250000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50597837206565561553/50000000000000000000 : ℝ) ≤ (5014789682006533/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50597837206565561553/50000000000000000000 : ℝ)^512 ≤ (5014789682006533/5000000000000000 : ℝ)^2065 := by
      have hnat : (50597837206565561553 : ℕ)^512*5000000000000000^2065 ≤ 5014789682006533^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50597837206565561553 50000000000000000000 5014789682006533 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014789682006533/5000000000000000 : ℝ)) (X := (50597837206565561553/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19358931/20000000000000000000 : ℝ) ≤ ((9331896472230450429/9332000000000000000 : ℝ)+2*(14789682004133/2799600000000000 : ℝ)*(21/20000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (9331896472230450429/9332000000000000000 : ℝ)+2*(14789682004133/2799600000000000 : ℝ)*(21/20000 : ℝ)=(6250000000003/6250000000000 : ℝ) by norm_num, show 1+2*(19358931/20000000000000000000 : ℝ)=(10000000000019358931/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(597837206565561553/100000000000000000000 : ℝ)+(19358931/20000000000000000000 : ℝ) ≤ ((9331896472230450429/9332000000000000000 : ℝ)+(14789682004133/2799600000000000 : ℝ)*((28101/100000 : ℝ)+(21/20000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (9331896472230450429/9332000000000000000 : ℝ)+(14789682004133/2799600000000000 : ℝ)*((28101/100000 : ℝ)+(21/20000 : ℝ))=(10014789682008933/10000000000000000 : ℝ) by norm_num, show 1+(597837206565561553/100000000000000000000 : ℝ)+(19358931/20000000000000000000 : ℝ)=(6287364825416397263/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(597837206565561553/100000000000000000000 : ℝ) ≤ ((9331896472230450429/9332000000000000000 : ℝ)+2*(14789682004133/2799600000000000 : ℝ)*(28101/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (9331896472230450429/9332000000000000000 : ℝ)+2*(14789682004133/2799600000000000 : ℝ)*(28101/100000 : ℝ)=(5014789682006533/5000000000000000 : ℝ) by norm_num, show 1+2*(597837206565561553/100000000000000000000 : ℝ)=(50597837206565561553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9331896472230450429/9332000000000000000 : ℝ)*(X 1 0+X 2 0)+(14789682004133/2799600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (21/20000 : ℝ)) (hi := (28101/100000 : ℝ)) (c := (9331896472230450429/9332000000000000000 : ℝ)) (alpha := (14789682004133/2799600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9331896472230450429/9332000000000000000 : ℝ)*(X 0 1+X 2 1)+(14789682004133/2799600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (21/20000 : ℝ)) (hi := (28101/100000 : ℝ)) (c := (9331896472230450429/9332000000000000000 : ℝ)) (alpha := (14789682004133/2799600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9331896472230450429/9332000000000000000 : ℝ)*(X 0 2+X 1 2)+(14789682004133/2799600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (21/20000 : ℝ)) (hi := (28101/100000 : ℝ)) (c := (9331896472230450429/9332000000000000000 : ℝ)) (alpha := (14789682004133/2799600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531361833/2500000000 : ℝ)*X 0 0+(2860875129/5000000000 : ℝ)*X 0 1+(4986404933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1355799831/2500000000 : ℝ)*X 1 0+(-10095257/40000000 : ℝ)*X 1 1+(38956291/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67789999/125000000 : ℝ)*X 2 0+(155825143/312500000 : ℝ)*X 2 1+(-2523814323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135113733/312500000 : ℝ)*X 0 0+(1831473419/5000000000 : ℝ)*X 0 1+(127617303/250000000 : ℝ)*X 0 2+(135113733/312500000 : ℝ)*X 1 0+(1831473419/5000000000 : ℝ)*X 1 1+(127617303/250000000 : ℝ)*X 1 2+(135113733/312500000 : ℝ)*X 2 0+(1831473419/5000000000 : ℝ)*X 2 1+(127617303/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85054651/400000000 : ℝ)*X 0 0+(312295691/625000000 : ℝ)*X 0 1+(5711212281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1308845989/2500000000 : ℝ)*X 1 0+(-449751237/2500000000 : ℝ)*X 1 1+(2855607027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5235381913/10000000000 : ℝ)*X 2 0+(5711216313/10000000000 : ℝ)*X 2 1+(-1799004547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270339817/625000000 : ℝ)*X 0 0+(1016888577/2000000000 : ℝ)*X 0 1+(3683604401/10000000000 : ℝ)*X 0 2+(270339817/625000000 : ℝ)*X 1 0+(1016888577/2000000000 : ℝ)*X 1 1+(3683604401/10000000000 : ℝ)*X 1 2+(270339817/625000000 : ℝ)*X 2 0+(1016888577/2000000000 : ℝ)*X 2 1+(3683604401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((8641757/10000000000 : ℝ)*X 0 0+(686231649/1250000000 : ℝ)*X 0 1+(796676697/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((482176569/5000000000 : ℝ)*X 1 0+(-4457679629/10000000000 : ℝ)*X 1 1+(6927944261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((964346949/10000000000 : ℝ)*X 2 0+(692793089/1000000000 : ℝ)*X 2 1+(-4457698827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1924833357/10000000000 : ℝ)*X 0 0+(1166000497/2000000000 : ℝ)*X 0 1+(2510893099/5000000000 : ℝ)*X 0 2+(1924833357/10000000000 : ℝ)*X 1 0+(1166000497/2000000000 : ℝ)*X 1 1+(2510893099/5000000000 : ℝ)*X 1 2+(1924833357/10000000000 : ℝ)*X 2 0+(1166000497/2000000000 : ℝ)*X 2 1+(2510893099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4941256159212105129025845547/466600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1026758125033327/100000000000000 : ℝ)*(major0) + (1026758125033327/100000000000000 : ℝ)*(major1) + (1026758125033327/100000000000000 : ℝ)*(major2) + (679953855600253/50000000000000 : ℝ)*(sp0) + (1359908495914741/100000000000000 : ℝ)*(sp1) + (679953822722049/50000000000000 : ℝ)*(sp2) + (138720890977759/20000000000000 : ℝ)*(sp3) + (57993109/4000000000000 : ℝ)*(sp4) + (495125897/50000000000000 : ℝ)*(sp5) + (844177603/50000000000000 : ℝ)*(sp6) + (96658291/10000000000000 : ℝ)*(sp8) + (320722303/50000000000000 : ℝ)*(sp9) + (793811837/100000000000000 : ℝ)*(sp10) + (65728471/5000000000000 : ℝ)*(sp11) + (138721153891643/20000000000000 : ℝ)*(f.failure) + (1359910127611141/100000000000000 : ℝ)*(f.sum) + (57372527659751/139980000000000000000000000000 : ℝ)*base65 + (6055317643144548151/2799600000000000000000000000000000 : ℝ)*base68 + (6865627610038548151/2799600000000000000000000000000000 : ℝ)*base70 + (8663896618161348151/2799600000000000000000000000000000 : ℝ)*base72 + (13280251184029/139980000000000000000000000000 : ℝ)*base74 + (4382961442907748151/2799600000000000000000000000000000 : ℝ)*base76 + (4271242399851348151/2799600000000000000000000000000000 : ℝ)*base78 + (3301367887149348151/2799600000000000000000000000000000 : ℝ)*base80 + (49194747400991/139980000000000000000000000000 : ℝ)*base81 + (318921/2000000000000000000000 : ℝ)*base89 + (318921/2000000000000000000000 : ℝ)*base91 + (318921/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3173338311968541881508642321/466600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12789909/25000000000000 : ℝ)*(lower4) + (1056738768071139/100000000000000 : ℝ)*(major0) + (1056738768071139/100000000000000 : ℝ)*(major1) + (1056738768071139/100000000000000 : ℝ)*(major2) + (1612458739/100000000000000 : ℝ)*(sp0) + (691370891/25000000000000 : ℝ)*(sp1) + (1149923521/20000000000000 : ℝ)*(sp2) + (13996138537567/1000000000000 : ℝ)*(sp4) + (349903884128521/25000000000000 : ℝ)*(sp5) + (699806485430291/50000000000000 : ℝ)*(sp6) + (713856778982231/100000000000000 : ℝ)*(sp7) + (813565687/25000000000000 : ℝ)*(sp8) + (418480539/100000000000000 : ℝ)*(sp9) + (904991223/50000000000000 : ℝ)*(sp11) + (713858588964677/100000000000000 : ℝ)*(f.failure) + (1399618720478187/100000000000000 : ℝ)*(f.sum) + (317663256885891/46660000000000000000000000000 : ℝ)*base66 + (3169180302239758631/933200000000000000000000000000000 : ℝ)*base67 + (4803762456206558631/933200000000000000000000000000000 : ℝ)*base69 + (5332224935580158631/933200000000000000000000000000000 : ℝ)*base71 + (2915213779709/46660000000000000000000000000 : ℝ)*base73 + (4249947402080158631/933200000000000000000000000000000 : ℝ)*base75 + (6099393216719358631/933200000000000000000000000000000 : ℝ)*base77 + (3515338553862158631/933200000000000000000000000000000 : ℝ)*base79 + (7052112886371/46660000000000000000000000000 : ℝ)*base82 + (49463881/10000000000000000000000 : ℝ)*base90 + (49463881/10000000000000000000000 : ℝ)*base92 + (49463881/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1068_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (209/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1068_s2_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182754099/10000000000 : ℝ)*x 0 + (552548443/1000000000 : ℝ)*x 1 + (643288783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182754099/10000000000 : ℝ)^8261 ≤ (2643321735921/20000000000000 : ℝ)^6213 := by
    have hnat : (2182754099 : ℕ)^8261*20000000000000^6213 ≤ 2643321735921^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182754099 10000000000 2643321735921 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552548443/1000000000 : ℝ)^8261 ≤ (45440963965983/100000000000000 : ℝ)^6213 := by
    have hnat : (552548443 : ℕ)^8261*100000000000000^6213 ≤ 45440963965983^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552548443 1000000000 45440963965983 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643288783/1250000000 : ℝ)^8261 ≤ (10335606834071/25000000000000 : ℝ)^6213 := by
    have hnat : (643288783 : ℕ)^8261*25000000000000^6213 ≤ 10335606834071^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643288783 1250000000 10335606834071 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182754099/10000000000 : ℝ), (552548443/1000000000 : ℝ), (643288783/1250000000 : ℝ)] ![(2643321735921/20000000000000 : ℝ), (45440963965983/100000000000000 : ℝ), (10335606834071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182754099/10000000000 : ℝ)|^8261 ≤ (2643321735921/20000000000000 : ℝ)^6213
        have hw : |(-2182754099/10000000000 : ℝ)|=(2182754099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552548443/1000000000 : ℝ)|^8261 ≤ (45440963965983/100000000000000 : ℝ)^6213
        have hw : |(552548443/1000000000 : ℝ)|=(552548443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643288783/1250000000 : ℝ)|^8261 ≤ (10335606834071/25000000000000 : ℝ)^6213
        have hw : |(643288783/1250000000 : ℝ)|=(643288783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377112417/10000000000 : ℝ)*x 0 + (-2380478929/10000000000 : ℝ)*x 1 + (5146311431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377112417/10000000000 : ℝ)^8261 ≤ (21912889241769/50000000000000 : ℝ)^6213 := by
    have hnat : (5377112417 : ℕ)^8261*50000000000000^6213 ≤ 21912889241769^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377112417 10000000000 21912889241769 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2380478929/10000000000 : ℝ)^8261 ≤ (14831781698341/100000000000000 : ℝ)^6213 := by
    have hnat : (2380478929 : ℕ)^8261*100000000000000^6213 ≤ 14831781698341^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380478929 10000000000 14831781698341 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146311431/10000000000 : ℝ)^8261 ≤ (1291951243799/3125000000000 : ℝ)^6213 := by
    have hnat : (5146311431 : ℕ)^8261*3125000000000^6213 ≤ 1291951243799^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146311431 10000000000 1291951243799 3125000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377112417/10000000000 : ℝ), (-2380478929/10000000000 : ℝ), (5146311431/10000000000 : ℝ)] ![(21912889241769/50000000000000 : ℝ), (14831781698341/100000000000000 : ℝ), (1291951243799/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377112417/10000000000 : ℝ)|^8261 ≤ (21912889241769/50000000000000 : ℝ)^6213
        have hw : |(5377112417/10000000000 : ℝ)|=(5377112417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2380478929/10000000000 : ℝ)|^8261 ≤ (14831781698341/100000000000000 : ℝ)^6213
        have hw : |(-2380478929/10000000000 : ℝ)|=(2380478929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146311431/10000000000 : ℝ)|^8261 ≤ (1291951243799/3125000000000 : ℝ)^6213
        have hw : |(5146311431/10000000000 : ℝ)|=(5146311431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377112289/10000000000 : ℝ)*x 0 + (160822237/312500000 : ℝ)*x 1 + (-23804789/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377112289/10000000000 : ℝ)^8261 ≤ (21912888548197/50000000000000 : ℝ)^6213 := by
    have hnat : (5377112289 : ℕ)^8261*50000000000000^6213 ≤ 21912888548197^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377112289 10000000000 21912888548197 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160822237/312500000 : ℝ)^8261 ≤ (20671220717917/50000000000000 : ℝ)^6213 := by
    have hnat : (160822237 : ℕ)^8261*50000000000000^6213 ≤ 20671220717917^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160822237 312500000 20671220717917 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23804789/100000000 : ℝ)^8261 ≤ (7415890729047/50000000000000 : ℝ)^6213 := by
    have hnat : (23804789 : ℕ)^8261*50000000000000^6213 ≤ 7415890729047^6213*100000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23804789 100000000 7415890729047 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377112289/10000000000 : ℝ), (160822237/312500000 : ℝ), (-23804789/100000000 : ℝ)] ![(21912888548197/50000000000000 : ℝ), (20671220717917/50000000000000 : ℝ), (7415890729047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377112289/10000000000 : ℝ)|^8261 ≤ (21912888548197/50000000000000 : ℝ)^6213
        have hw : |(5377112289/10000000000 : ℝ)|=(5377112289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160822237/312500000 : ℝ)|^8261 ≤ (20671220717917/50000000000000 : ℝ)^6213
        have hw : |(160822237/312500000 : ℝ)|=(160822237/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23804789/100000000 : ℝ)|^8261 ≤ (7415890729047/50000000000000 : ℝ)^6213
        have hw : |(-23804789/100000000 : ℝ)|=(23804789/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090687677/2500000000 : ℝ)*x 0 + (2003500477/5000000000 : ℝ)*x 1 + (4750414391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090687677/2500000000 : ℝ)^8261 ≤ (16595261915449/50000000000000 : ℝ)^6213 := by
    have hnat : (1090687677 : ℕ)^8261*50000000000000^6213 ≤ 16595261915449^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090687677 2500000000 16595261915449 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003500477/5000000000 : ℝ)^8261 ≤ (5928246481653/20000000000000 : ℝ)^6213 := by
    have hnat : (2003500477 : ℕ)^8261*20000000000000^6213 ≤ 5928246481653^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003500477 5000000000 5928246481653 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4750414391/10000000000 : ℝ)^8261 ≤ (37168243745139/100000000000000 : ℝ)^6213 := by
    have hnat : (4750414391 : ℕ)^8261*100000000000000^6213 ≤ 37168243745139^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750414391 10000000000 37168243745139 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090687677/2500000000 : ℝ), (2003500477/5000000000 : ℝ), (4750414391/10000000000 : ℝ)] ![(16595261915449/50000000000000 : ℝ), (5928246481653/20000000000000 : ℝ), (37168243745139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090687677/2500000000 : ℝ)|^8261 ≤ (16595261915449/50000000000000 : ℝ)^6213
        have hw : |(1090687677/2500000000 : ℝ)|=(1090687677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003500477/5000000000 : ℝ)|^8261 ≤ (5928246481653/20000000000000 : ℝ)^6213
        have hw : |(2003500477/5000000000 : ℝ)|=(2003500477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4750414391/10000000000 : ℝ)|^8261 ≤ (37168243745139/100000000000000 : ℝ)^6213
        have hw : |(4750414391/10000000000 : ℝ)|=(4750414391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-545719751/2500000000 : ℝ)*x 0 + (5149066259/10000000000 : ℝ)*x 1 + (2761349917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545719751/2500000000 : ℝ)^8261 ≤ (13217614291513/100000000000000 : ℝ)^6213 := by
    have hnat : (545719751 : ℕ)^8261*100000000000000^6213 ≤ 13217614291513^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545719751 2500000000 13217614291513 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149066259/10000000000 : ℝ)^8261 ≤ (41371868029111/100000000000000 : ℝ)^6213 := by
    have hnat : (5149066259 : ℕ)^8261*100000000000000^6213 ≤ 41371868029111^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149066259 10000000000 41371868029111 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761349917/5000000000 : ℝ)^8261 ≤ (22705258831607/50000000000000 : ℝ)^6213 := by
    have hnat : (2761349917 : ℕ)^8261*50000000000000^6213 ≤ 22705258831607^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761349917 5000000000 22705258831607 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545719751/2500000000 : ℝ), (5149066259/10000000000 : ℝ), (2761349917/5000000000 : ℝ)] ![(13217614291513/100000000000000 : ℝ), (41371868029111/100000000000000 : ℝ), (22705258831607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545719751/2500000000 : ℝ)|^8261 ≤ (13217614291513/100000000000000 : ℝ)^6213
        have hw : |(-545719751/2500000000 : ℝ)|=(545719751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149066259/10000000000 : ℝ)|^8261 ≤ (41371868029111/100000000000000 : ℝ)^6213
        have hw : |(5149066259/10000000000 : ℝ)|=(5149066259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2761349917/5000000000 : ℝ)|^8261 ≤ (22705258831607/50000000000000 : ℝ)^6213
        have hw : |(2761349917/5000000000 : ℝ)|=(2761349917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320347793/2500000000 : ℝ)*x 0 + (-125255761/625000000 : ℝ)*x 1 + (5522699921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320347793/2500000000 : ℝ)^8261 ≤ (21395748294503/50000000000000 : ℝ)^6213 := by
    have hnat : (1320347793 : ℕ)^8261*50000000000000^6213 ≤ 21395748294503^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320347793 2500000000 21395748294503 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125255761/625000000 : ℝ)^8261 ≤ (11797984782569/100000000000000 : ℝ)^6213 := by
    have hnat : (125255761 : ℕ)^8261*100000000000000^6213 ≤ 11797984782569^6213*625000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125255761 625000000 11797984782569 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522699921/10000000000 : ℝ)^8261 ≤ (45410518614379/100000000000000 : ℝ)^6213 := by
    have hnat : (5522699921 : ℕ)^8261*100000000000000^6213 ≤ 45410518614379^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522699921 10000000000 45410518614379 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320347793/2500000000 : ℝ), (-125255761/625000000 : ℝ), (5522699921/10000000000 : ℝ)] ![(21395748294503/50000000000000 : ℝ), (11797984782569/100000000000000 : ℝ), (45410518614379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320347793/2500000000 : ℝ)|^8261 ≤ (21395748294503/50000000000000 : ℝ)^6213
        have hw : |(1320347793/2500000000 : ℝ)|=(1320347793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125255761/625000000 : ℝ)|^8261 ≤ (11797984782569/100000000000000 : ℝ)^6213
        have hw : |(-125255761/625000000 : ℝ)|=(125255761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522699921/10000000000 : ℝ)|^8261 ≤ (45410518614379/100000000000000 : ℝ)^6213
        have hw : |(5522699921/10000000000 : ℝ)|=(5522699921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281391417/10000000000 : ℝ)*x 0 + (2761349879/5000000000 : ℝ)*x 1 + (-2004092067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281391417/10000000000 : ℝ)^8261 ≤ (21395749614207/50000000000000 : ℝ)^6213 := by
    have hnat : (5281391417 : ℕ)^8261*50000000000000^6213 ≤ 21395749614207^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281391417 10000000000 21395749614207 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761349879/5000000000 : ℝ)^8261 ≤ (5676314604039/12500000000000 : ℝ)^6213 := by
    have hnat : (2761349879 : ℕ)^8261*12500000000000^6213 ≤ 5676314604039^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761349879 5000000000 5676314604039 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004092067/10000000000 : ℝ)^8261 ≤ (5898991964687/50000000000000 : ℝ)^6213 := by
    have hnat : (2004092067 : ℕ)^8261*50000000000000^6213 ≤ 5898991964687^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004092067 10000000000 5898991964687 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281391417/10000000000 : ℝ), (2761349879/5000000000 : ℝ), (-2004092067/10000000000 : ℝ)] ![(21395749614207/50000000000000 : ℝ), (5676314604039/12500000000000 : ℝ), (5898991964687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281391417/10000000000 : ℝ)|^8261 ≤ (21395749614207/50000000000000 : ℝ)^6213
        have hw : |(5281391417/10000000000 : ℝ)|=(5281391417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761349879/5000000000 : ℝ)|^8261 ≤ (5676314604039/12500000000000 : ℝ)^6213
        have hw : |(2761349879/5000000000 : ℝ)|=(2761349879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2004092067/10000000000 : ℝ)|^8261 ≤ (5898991964687/50000000000000 : ℝ)^6213
        have hw : |(-2004092067/10000000000 : ℝ)|=(2004092067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362993609/10000000000 : ℝ)*x 0 + (2372508877/5000000000 : ℝ)*x 1 + (401245689/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362993609/10000000000 : ℝ)^8261 ≤ (33192980905063/100000000000000 : ℝ)^6213 := by
    have hnat : (4362993609 : ℕ)^8261*100000000000000^6213 ≤ 33192980905063^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362993609 10000000000 33192980905063 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2372508877/5000000000 : ℝ)^8261 ≤ (9278027834203/25000000000000 : ℝ)^6213 := by
    have hnat : (2372508877 : ℕ)^8261*25000000000000^6213 ≤ 9278027834203^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2372508877 5000000000 9278027834203 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401245689/1000000000 : ℝ)^8261 ≤ (29694907743727/100000000000000 : ℝ)^6213 := by
    have hnat : (401245689 : ℕ)^8261*100000000000000^6213 ≤ 29694907743727^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401245689 1000000000 29694907743727 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362993609/10000000000 : ℝ), (2372508877/5000000000 : ℝ), (401245689/1000000000 : ℝ)] ![(33192980905063/100000000000000 : ℝ), (9278027834203/25000000000000 : ℝ), (29694907743727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362993609/10000000000 : ℝ)|^8261 ≤ (33192980905063/100000000000000 : ℝ)^6213
        have hw : |(4362993609/10000000000 : ℝ)|=(4362993609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2372508877/5000000000 : ℝ)|^8261 ≤ (9278027834203/25000000000000 : ℝ)^6213
        have hw : |(2372508877/5000000000 : ℝ)|=(2372508877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401245689/1000000000 : ℝ)|^8261 ≤ (29694907743727/100000000000000 : ℝ)^6213
        have hw : |(401245689/1000000000 : ℝ)|=(401245689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_8 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-49613153/5000000000 : ℝ)*x 0 + (2963919633/5000000000 : ℝ)*x 1 + (2963827951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49613153/5000000000 : ℝ)^8261 ≤ (54224067427/25000000000000 : ℝ)^6213 := by
    have hnat : (49613153 : ℕ)^8261*25000000000000^6213 ≤ 54224067427^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49613153 5000000000 54224067427 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963919633/5000000000 : ℝ)^8261 ≤ (12473144467277/25000000000000 : ℝ)^6213 := by
    have hnat : (2963919633 : ℕ)^8261*25000000000000^6213 ≤ 12473144467277^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963919633 5000000000 12473144467277 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2963827951/5000000000 : ℝ)^8261 ≤ (623631573051/1250000000000 : ℝ)^6213 := by
    have hnat : (2963827951 : ℕ)^8261*1250000000000^6213 ≤ 623631573051^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963827951 5000000000 623631573051 1250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49613153/5000000000 : ℝ), (2963919633/5000000000 : ℝ), (2963827951/5000000000 : ℝ)] ![(54224067427/25000000000000 : ℝ), (12473144467277/25000000000000 : ℝ), (623631573051/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49613153/5000000000 : ℝ)|^8261 ≤ (54224067427/25000000000000 : ℝ)^6213
        have hw : |(-49613153/5000000000 : ℝ)|=(49613153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963919633/5000000000 : ℝ)|^8261 ≤ (12473144467277/25000000000000 : ℝ)^6213
        have hw : |(2963919633/5000000000 : ℝ)|=(2963919633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2963827951/5000000000 : ℝ)|^8261 ≤ (623631573051/1250000000000 : ℝ)^6213
        have hw : |(2963827951/5000000000 : ℝ)|=(2963827951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_9 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (99283983/1250000000 : ℝ)*x 0 + (-124265837/250000000 : ℝ)*x 1 + (6558997851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99283983/1250000000 : ℝ)^8261 ≤ (3446390297869/100000000000000 : ℝ)^6213 := by
    have hnat : (99283983 : ℕ)^8261*100000000000000^6213 ≤ 3446390297869^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99283983 1250000000 3446390297869 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124265837/250000000 : ℝ)^8261 ≤ (4934572400053/12500000000000 : ℝ)^6213 := by
    have hnat : (124265837 : ℕ)^8261*12500000000000^6213 ≤ 4934572400053^6213*250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124265837 250000000 4934572400053 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6558997851/10000000000 : ℝ)^8261 ≤ (3567314405507/6250000000000 : ℝ)^6213 := by
    have hnat : (6558997851 : ℕ)^8261*6250000000000^6213 ≤ 3567314405507^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6558997851 10000000000 3567314405507 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99283983/1250000000 : ℝ), (-124265837/250000000 : ℝ), (6558997851/10000000000 : ℝ)] ![(3446390297869/100000000000000 : ℝ), (4934572400053/12500000000000 : ℝ), (3567314405507/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99283983/1250000000 : ℝ)|^8261 ≤ (3446390297869/100000000000000 : ℝ)^6213
        have hw : |(99283983/1250000000 : ℝ)|=(99283983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124265837/250000000 : ℝ)|^8261 ≤ (4934572400053/12500000000000 : ℝ)^6213
        have hw : |(-124265837/250000000 : ℝ)|=(124265837/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6558997851/10000000000 : ℝ)|^8261 ≤ (3567314405507/6250000000000 : ℝ)^6213
        have hw : |(6558997851/10000000000 : ℝ)|=(6558997851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_10 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (792898221/10000000000 : ℝ)*x 0 + (6555460219/10000000000 : ℝ)*x 1 + (-4975258919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792898221/10000000000 : ℝ)^8261 ≤ (214904221037/6250000000000 : ℝ)^6213 := by
    have hnat : (792898221 : ℕ)^8261*6250000000000^6213 ≤ 214904221037^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792898221 10000000000 214904221037 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6555460219/10000000000 : ℝ)^8261 ≤ (14259025417797/25000000000000 : ℝ)^6213 := by
    have hnat : (6555460219 : ℕ)^8261*25000000000000^6213 ≤ 14259025417797^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6555460219 10000000000 14259025417797 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4975258919/10000000000 : ℝ)^8261 ≤ (39525430777289/100000000000000 : ℝ)^6213 := by
    have hnat : (4975258919 : ℕ)^8261*100000000000000^6213 ≤ 39525430777289^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975258919 10000000000 39525430777289 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792898221/10000000000 : ℝ), (6555460219/10000000000 : ℝ), (-4975258919/10000000000 : ℝ)] ![(214904221037/6250000000000 : ℝ), (14259025417797/25000000000000 : ℝ), (39525430777289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792898221/10000000000 : ℝ)|^8261 ≤ (214904221037/6250000000000 : ℝ)^6213
        have hw : |(792898221/10000000000 : ℝ)|=(792898221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6555460219/10000000000 : ℝ)|^8261 ≤ (14259025417797/25000000000000 : ℝ)^6213
        have hw : |(6555460219/10000000000 : ℝ)|=(6555460219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4975258919/10000000000 : ℝ)|^8261 ≤ (39525430777289/100000000000000 : ℝ)^6213
        have hw : |(-4975258919/10000000000 : ℝ)|=(4975258919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s2_11 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (210111221/5000000000 : ℝ)*x 0 + (2934680181/5000000000 : ℝ)*x 1 + (2936624767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210111221/5000000000 : ℝ)^8261 ≤ (184775661581/12500000000000 : ℝ)^6213 := by
    have hnat : (210111221 : ℕ)^8261*12500000000000^6213 ≤ 184775661581^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210111221 5000000000 184775661581 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934680181/5000000000 : ℝ)^8261 ≤ (24619602011793/50000000000000 : ℝ)^6213 := by
    have hnat : (2934680181 : ℕ)^8261*50000000000000^6213 ≤ 24619602011793^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934680181 5000000000 24619602011793 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2936624767/5000000000 : ℝ)^8261 ≤ (24641295335269/50000000000000 : ℝ)^6213 := by
    have hnat : (2936624767 : ℕ)^8261*50000000000000^6213 ≤ 24641295335269^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2936624767 5000000000 24641295335269 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210111221/5000000000 : ℝ), (2934680181/5000000000 : ℝ), (2936624767/5000000000 : ℝ)] ![(184775661581/12500000000000 : ℝ), (24619602011793/50000000000000 : ℝ), (24641295335269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210111221/5000000000 : ℝ)|^8261 ≤ (184775661581/12500000000000 : ℝ)^6213
        have hw : |(210111221/5000000000 : ℝ)|=(210111221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934680181/5000000000 : ℝ)|^8261 ≤ (24619602011793/50000000000000 : ℝ)^6213
        have hw : |(2934680181/5000000000 : ℝ)|=(2934680181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2936624767/5000000000 : ℝ)|^8261 ≤ (24641295335269/50000000000000 : ℝ)^6213
        have hw : |(2936624767/5000000000 : ℝ)|=(2936624767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (4361/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (209/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (209/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (209/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (209/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (209/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (209/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (209/4000 : ℝ) ^ (2065/512 : ℝ) ≤ (675743128502259/100000000000000000000 : ℝ) := by
    have hpowers : (209/4000 : ℝ)^2065 ≤ (675743128502259/100000000000000000000 : ℝ)^512 := by
      have hnat : (209 : ℕ)^2065*100000000000000000000^512 ≤ 675743128502259^512*4000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        209 4000 675743128502259 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (209/4000 : ℝ)) (X := (675743128502259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20781/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (177015038150781847/100000000000000000000 : ℝ) := by
    have hpowers : (20781/100000 : ℝ)^2065 ≤ (177015038150781847/100000000000000000000 : ℝ)^512 := by
      have hnat : (20781 : ℕ)^2065*100000000000000000000^512 ≤ 177015038150781847^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20781 100000 177015038150781847 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20781/100000 : ℝ)) (X := (177015038150781847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000675743128502259/50000000000000000000 : ℝ) ≤ (1000003350883521/1000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50000675743128502259/50000000000000000000 : ℝ)^512 ≤ (1000003350883521/1000000000000000 : ℝ)^2065 := by
      have hnat : (50000675743128502259 : ℕ)^512*1000000000000000^2065 ≤ 1000003350883521^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000675743128502259 50000000000000000000 1000003350883521 1000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000003350883521/1000000000000000 : ℝ)) (X := (50000675743128502259/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50088845390639642053/50000000000000000000 : ℝ) ≤ (1250550344761251/1250000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50088845390639642053/50000000000000000000 : ℝ)^512 ≤ (1250550344761251/1250000000000000 : ℝ)^2065 := by
      have hnat : (50088845390639642053 : ℕ)^512*1250000000000000^2065 ≤ 1250550344761251^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50088845390639642053 50000000000000000000 1250550344761251 1250000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250550344761251/1250000000000000 : ℝ)) (X := (50088845390639642053/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50177015038150781847/50000000000000000000 : ℝ) ≤ (5004386003672403/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50177015038150781847/50000000000000000000 : ℝ)^512 ≤ (5004386003672403/5000000000000000 : ℝ)^2065 := by
      have hnat : (50177015038150781847 : ℕ)^512*5000000000000000^2065 ≤ 5004386003672403^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50177015038150781847 50000000000000000000 5004386003672403 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004386003672403/5000000000000000 : ℝ)) (X := (50177015038150781847/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(675743128502259/100000000000000000000 : ℝ) ≤ ((7775743130436394383/7778000000000000000 : ℝ)+2*(2184624627399/777800000000000 : ℝ)*(209/4000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (7775743130436394383/7778000000000000000 : ℝ)+2*(2184624627399/777800000000000 : ℝ)*(209/4000 : ℝ)=(1000003350883521/1000000000000000 : ℝ) by norm_num, show 1+2*(675743128502259/100000000000000000000 : ℝ)=(50000675743128502259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(177015038150781847/100000000000000000000 : ℝ)+(675743128502259/100000000000000000000 : ℝ) ≤ ((7775743130436394383/7778000000000000000 : ℝ)+(2184624627399/777800000000000 : ℝ)*((20781/100000 : ℝ)+(209/4000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (7775743130436394383/7778000000000000000 : ℝ)+(2184624627399/777800000000000 : ℝ)*((20781/100000 : ℝ)+(209/4000 : ℝ))=(1250550344761251/1250000000000000 : ℝ) by norm_num, show 1+(177015038150781847/100000000000000000000 : ℝ)+(675743128502259/100000000000000000000 : ℝ)=(50088845390639642053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(177015038150781847/100000000000000000000 : ℝ) ≤ ((7775743130436394383/7778000000000000000 : ℝ)+2*(2184624627399/777800000000000 : ℝ)*(20781/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (7775743130436394383/7778000000000000000 : ℝ)+2*(2184624627399/777800000000000 : ℝ)*(20781/100000 : ℝ)=(5004386003672403/5000000000000000 : ℝ) by norm_num, show 1+2*(177015038150781847/100000000000000000000 : ℝ)=(50177015038150781847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7775743130436394383/7778000000000000000 : ℝ)*(X 1 0+X 2 0)+(2184624627399/777800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (209/4000 : ℝ)) (hi := (20781/100000 : ℝ)) (c := (7775743130436394383/7778000000000000000 : ℝ)) (alpha := (2184624627399/777800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7775743130436394383/7778000000000000000 : ℝ)*(X 0 1+X 2 1)+(2184624627399/777800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (209/4000 : ℝ)) (hi := (20781/100000 : ℝ)) (c := (7775743130436394383/7778000000000000000 : ℝ)) (alpha := (2184624627399/777800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7775743130436394383/7778000000000000000 : ℝ)*(X 0 2+X 1 2)+(2184624627399/777800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (209/4000 : ℝ)) (hi := (20781/100000 : ℝ)) (c := (7775743130436394383/7778000000000000000 : ℝ)) (alpha := (2184624627399/777800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2182754099/10000000000 : ℝ)*X 0 0+(552548443/1000000000 : ℝ)*X 0 1+(643288783/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377112417/10000000000 : ℝ)*X 1 0+(-2380478929/10000000000 : ℝ)*X 1 1+(5146311431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377112289/10000000000 : ℝ)*X 2 0+(160822237/312500000 : ℝ)*X 2 1+(-23804789/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090687677/2500000000 : ℝ)*X 0 0+(2003500477/5000000000 : ℝ)*X 0 1+(4750414391/10000000000 : ℝ)*X 0 2+(1090687677/2500000000 : ℝ)*X 1 0+(2003500477/5000000000 : ℝ)*X 1 1+(4750414391/10000000000 : ℝ)*X 1 2+(1090687677/2500000000 : ℝ)*X 2 0+(2003500477/5000000000 : ℝ)*X 2 1+(4750414391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-545719751/2500000000 : ℝ)*X 0 0+(5149066259/10000000000 : ℝ)*X 0 1+(2761349917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320347793/2500000000 : ℝ)*X 1 0+(-125255761/625000000 : ℝ)*X 1 1+(5522699921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5281391417/10000000000 : ℝ)*X 2 0+(2761349879/5000000000 : ℝ)*X 2 1+(-2004092067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362993609/10000000000 : ℝ)*X 0 0+(2372508877/5000000000 : ℝ)*X 0 1+(401245689/1000000000 : ℝ)*X 0 2+(4362993609/10000000000 : ℝ)*X 1 0+(2372508877/5000000000 : ℝ)*X 1 1+(401245689/1000000000 : ℝ)*X 1 2+(4362993609/10000000000 : ℝ)*X 2 0+(2372508877/5000000000 : ℝ)*X 2 1+(401245689/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-49613153/5000000000 : ℝ)*X 0 0+(2963919633/5000000000 : ℝ)*X 0 1+(2963827951/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((99283983/1250000000 : ℝ)*X 1 0+(-124265837/250000000 : ℝ)*X 1 1+(6558997851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((792898221/10000000000 : ℝ)*X 2 0+(6555460219/10000000000 : ℝ)*X 2 1+(-4975258919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((210111221/5000000000 : ℝ)*X 0 0+(2934680181/5000000000 : ℝ)*X 0 1+(2936624767/5000000000 : ℝ)*X 0 2+(210111221/5000000000 : ℝ)*X 1 0+(2934680181/5000000000 : ℝ)*X 1 1+(2936624767/5000000000 : ℝ)*X 1 2+(210111221/5000000000 : ℝ)*X 2 0+(2934680181/5000000000 : ℝ)*X 2 1+(2936624767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (928935882766217126489212221/388900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1991248622841957/100000000000000 : ℝ)*(major0) + (1991248622841957/100000000000000 : ℝ)*(major1) + (1991248622841957/100000000000000 : ℝ)*(major2) + (2637329195006177/100000000000000 : ℝ)*(sp0) + (1318669642903709/50000000000000 : ℝ)*(sp1) + (2637340062741793/100000000000000 : ℝ)*(sp2) + (672573289057347/50000000000000 : ℝ)*(sp3) + (1887455383/10000000000000 : ℝ)*(sp4) + (352763723/4000000000000 : ℝ)*(sp5) + (4050577751/50000000000000 : ℝ)*(sp6) + (1198906401/100000000000000 : ℝ)*(sp8) + (232713183/20000000000000 : ℝ)*(sp9) + (1104569113/100000000000000 : ℝ)*(sp10) + (659741001/50000000000000 : ℝ)*(sp11) + (1345147897596697/100000000000000 : ℝ)*(f.failure) + (329668658558301/12500000000000 : ℝ)*(f.sum) + (32404932982413/38890000000000000000000000000 : ℝ)*base65 + (6066924552651157531/777800000000000000000000000000000 : ℝ)*base67 + (9696037051728357531/777800000000000000000000000000000 : ℝ)*base69 + (1045260725974357531/777800000000000000000000000000000 : ℝ)*base71 + (108852585266423/38890000000000000000000000000 : ℝ)*base73 + (8095949032233957531/777800000000000000000000000000000 : ℝ)*base75 + (10266227727313957531/777800000000000000000000000000000 : ℝ)*base77 + (5029240860614957531/777800000000000000000000000000000 : ℝ)*base79 + (220389215597353/38890000000000000000000000000 : ℝ)*base81 + (22320941/10000000000000000000000 : ℝ)*base90 + (22320941/10000000000000000000000 : ℝ)*base92 + (22320941/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373626579439966502695052517/48612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252593505791189/12500000000000 : ℝ)*(major0) + (252593505791189/12500000000000 : ℝ)*(major1) + (252593505791189/12500000000000 : ℝ)*(major2) + (332262913/50000000000000 : ℝ)*(sp1) + (15282793/12500000000000 : ℝ)*(sp2) + (38274557/12500000000000 : ℝ)*(sp3) + (334552407019547/12500000000000 : ℝ)*(sp4) + (1338209574239607/50000000000000 : ℝ)*(sp5) + (1338209778167451/50000000000000 : ℝ)*(sp6) + (682537365709659/50000000000000 : ℝ)*(sp7) + (37655189/4000000000000 : ℝ)*(sp8) + (384531061/100000000000000 : ℝ)*(sp9) + (103787771/20000000000000 : ℝ)*(sp10) + (601313377/100000000000000 : ℝ)*(sp11) + (1365075638929151/100000000000000 : ℝ)*(f.failure) + (1338210098768051/50000000000000 : ℝ)*(f.sum) + (39667796155953/9722500000000000000000000000 : ℝ)*base66 + (412027582523201387/97225000000000000000000000000000 : ℝ)*base67 + (437997190490801387/97225000000000000000000000000000 : ℝ)*base69 + (493606008296551387/97225000000000000000000000000000 : ℝ)*base71 + (250378421931/1215312500000000000000000000 : ℝ)*base74 + (868161378614476387/97225000000000000000000000000000 : ℝ)*base75 + (910826624975576387/97225000000000000000000000000000 : ℝ)*base77 + (787135572352026387/97225000000000000000000000000000 : ℝ)*base79 + (29447365460831/19445000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17586997/10000000000000000000000 : ℝ)*base89 + (17586997/10000000000000000000000 : ℝ)*base91 + (17586997/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1068_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1068_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1068_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1068_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1068_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4361/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8367/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

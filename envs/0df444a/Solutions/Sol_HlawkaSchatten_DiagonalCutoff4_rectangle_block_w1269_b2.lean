-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1269_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:07.496348+00:00
-- url     : https://prove2.me/submissions/fdcb5ea9-ce3c-49a8-9f89-01e369f7171f

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
theorem support_rectangle_w1269_s6_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526617939/2500000000 : ℝ)*x 0 + (2708196769/5000000000 : ℝ)*x 1 + (1310531517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526617939/2500000000 : ℝ)^8463 ≤ (6405744268013/50000000000000 : ℝ)^6415 := by
    have hnat : (526617939 : ℕ)^8463*50000000000000^6415 ≤ 6405744268013^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526617939 2500000000 6405744268013 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708196769/5000000000 : ℝ)^8463 ≤ (44534515227731/100000000000000 : ℝ)^6415 := by
    have hnat : (2708196769 : ℕ)^8463*100000000000000^6415 ≤ 44534515227731^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708196769 5000000000 44534515227731 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310531517/2500000000 : ℝ)^8463 ≤ (21326998111093/50000000000000 : ℝ)^6415 := by
    have hnat : (1310531517 : ℕ)^8463*50000000000000^6415 ≤ 21326998111093^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310531517 2500000000 21326998111093 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526617939/2500000000 : ℝ), (2708196769/5000000000 : ℝ), (1310531517/2500000000 : ℝ)] ![(6405744268013/50000000000000 : ℝ), (44534515227731/100000000000000 : ℝ), (21326998111093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526617939/2500000000 : ℝ)|^8463 ≤ (6405744268013/50000000000000 : ℝ)^6415
        have hw : |(-526617939/2500000000 : ℝ)|=(526617939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708196769/5000000000 : ℝ)|^8463 ≤ (44534515227731/100000000000000 : ℝ)^6415
        have hw : |(2708196769/5000000000 : ℝ)|=(2708196769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310531517/2500000000 : ℝ)|^8463 ≤ (21326998111093/50000000000000 : ℝ)^6415
        have hw : |(1310531517/2500000000 : ℝ)|=(1310531517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070020151/2000000000 : ℝ)*x 0 + (-2195324169/10000000000 : ℝ)*x 1 + (26210631/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070020151/2000000000 : ℝ)^8463 ≤ (10954209666863/25000000000000 : ℝ)^6415 := by
    have hnat : (1070020151 : ℕ)^8463*25000000000000^6415 ≤ 10954209666863^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070020151 2000000000 10954209666863 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195324169/10000000000 : ℝ)^8463 ≤ (13529163668893/100000000000000 : ℝ)^6415 := by
    have hnat : (2195324169 : ℕ)^8463*100000000000000^6415 ≤ 13529163668893^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195324169 10000000000 13529163668893 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26210631/50000000 : ℝ)^8463 ≤ (21326998819567/50000000000000 : ℝ)^6415 := by
    have hnat : (26210631 : ℕ)^8463*50000000000000^6415 ≤ 21326998819567^6415*50000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26210631 50000000 21326998819567 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070020151/2000000000 : ℝ), (-2195324169/10000000000 : ℝ), (26210631/50000000 : ℝ)] ![(10954209666863/25000000000000 : ℝ), (13529163668893/100000000000000 : ℝ), (21326998819567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070020151/2000000000 : ℝ)|^8463 ≤ (10954209666863/25000000000000 : ℝ)^6415
        have hw : |(1070020151/2000000000 : ℝ)|=(1070020151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195324169/10000000000 : ℝ)|^8463 ≤ (13529163668893/100000000000000 : ℝ)^6415
        have hw : |(-2195324169/10000000000 : ℝ)|=(2195324169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26210631/50000000 : ℝ)|^8463 ≤ (21326998819567/50000000000000 : ℝ)^6415
        have hw : |(26210631/50000000 : ℝ)|=(26210631/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267505037/500000000 : ℝ)*x 0 + (5242126173/10000000000 : ℝ)*x 1 + (-1097662113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267505037/500000000 : ℝ)^8463 ≤ (5477104813173/12500000000000 : ℝ)^6415 := by
    have hnat : (267505037 : ℕ)^8463*12500000000000^6415 ≤ 5477104813173^6415*500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267505037 500000000 5477104813173 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242126173/10000000000 : ℝ)^8463 ≤ (5331749668663/12500000000000 : ℝ)^6415 := by
    have hnat : (5242126173 : ℕ)^8463*12500000000000^6415 ≤ 5331749668663^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242126173 10000000000 5331749668663 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097662113/5000000000 : ℝ)^8463 ≤ (13529164132313/100000000000000 : ℝ)^6415 := by
    have hnat : (1097662113 : ℕ)^8463*100000000000000^6415 ≤ 13529164132313^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097662113 5000000000 13529164132313 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267505037/500000000 : ℝ), (5242126173/10000000000 : ℝ), (-1097662113/5000000000 : ℝ)] ![(5477104813173/12500000000000 : ℝ), (5331749668663/12500000000000 : ℝ), (13529164132313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267505037/500000000 : ℝ)|^8463 ≤ (5477104813173/12500000000000 : ℝ)^6415
        have hw : |(267505037/500000000 : ℝ)|=(267505037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242126173/10000000000 : ℝ)|^8463 ≤ (5331749668663/12500000000000 : ℝ)^6415
        have hw : |(5242126173/10000000000 : ℝ)|=(5242126173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097662113/5000000000 : ℝ)|^8463 ≤ (13529164132313/100000000000000 : ℝ)^6415
        have hw : |(-1097662113/5000000000 : ℝ)|=(1097662113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345390829/10000000000 : ℝ)*x 0 + (4171217293/10000000000 : ℝ)*x 1 + (4526574187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345390829/10000000000 : ℝ)^8463 ≤ (33301892681341/100000000000000 : ℝ)^6415 := by
    have hnat : (4345390829 : ℕ)^8463*100000000000000^6415 ≤ 33301892681341^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345390829 10000000000 33301892681341 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171217293/10000000000 : ℝ)^8463 ≤ (6310460425543/20000000000000 : ℝ)^6415 := by
    have hnat : (4171217293 : ℕ)^8463*20000000000000^6415 ≤ 6310460425543^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171217293 10000000000 6310460425543 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526574187/10000000000 : ℝ)^8463 ≤ (35145805170287/100000000000000 : ℝ)^6415 := by
    have hnat : (4526574187 : ℕ)^8463*100000000000000^6415 ≤ 35145805170287^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526574187 10000000000 35145805170287 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345390829/10000000000 : ℝ), (4171217293/10000000000 : ℝ), (4526574187/10000000000 : ℝ)] ![(33301892681341/100000000000000 : ℝ), (6310460425543/20000000000000 : ℝ), (35145805170287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345390829/10000000000 : ℝ)|^8463 ≤ (33301892681341/100000000000000 : ℝ)^6415
        have hw : |(4345390829/10000000000 : ℝ)|=(4345390829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171217293/10000000000 : ℝ)|^8463 ≤ (6310460425543/20000000000000 : ℝ)^6415
        have hw : |(4171217293/10000000000 : ℝ)|=(4171217293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526574187/10000000000 : ℝ)|^8463 ≤ (35145805170287/100000000000000 : ℝ)^6415
        have hw : |(4526574187/10000000000 : ℝ)|=(4526574187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053242349/5000000000 : ℝ)*x 0 + (1310686837/2500000000 : ℝ)*x 1 + (2707884557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053242349/5000000000 : ℝ)^8463 ≤ (3202898094531/25000000000000 : ℝ)^6415 := by
    have hnat : (1053242349 : ℕ)^8463*25000000000000^6415 ≤ 3202898094531^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053242349 5000000000 3202898094531 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310686837/2500000000 : ℝ)^8463 ≤ (42660665449717/100000000000000 : ℝ)^6415 := by
    have hnat : (1310686837 : ℕ)^8463*100000000000000^6415 ≤ 42660665449717^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310686837 2500000000 42660665449717 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707884557/5000000000 : ℝ)^8463 ≤ (11131935538541/25000000000000 : ℝ)^6415 := by
    have hnat : (2707884557 : ℕ)^8463*25000000000000^6415 ≤ 11131935538541^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707884557 5000000000 11131935538541 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053242349/5000000000 : ℝ), (1310686837/2500000000 : ℝ), (2707884557/5000000000 : ℝ)] ![(3202898094531/25000000000000 : ℝ), (42660665449717/100000000000000 : ℝ), (11131935538541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053242349/5000000000 : ℝ)|^8463 ≤ (3202898094531/25000000000000 : ℝ)^6415
        have hw : |(-1053242349/5000000000 : ℝ)|=(1053242349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310686837/2500000000 : ℝ)|^8463 ≤ (42660665449717/100000000000000 : ℝ)^6415
        have hw : |(1310686837/2500000000 : ℝ)|=(1310686837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707884557/5000000000 : ℝ)|^8463 ≤ (11131935538541/25000000000000 : ℝ)^6415
        have hw : |(2707884557/5000000000 : ℝ)|=(2707884557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305601939/10000000000 : ℝ)*x 0 + (-2021681127/10000000000 : ℝ)*x 1 + (5415768993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305601939/10000000000 : ℝ)^8463 ≤ (21668344219651/50000000000000 : ℝ)^6415 := by
    have hnat : (5305601939 : ℕ)^8463*50000000000000^6415 ≤ 21668344219651^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305601939 10000000000 21668344219651 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2021681127/10000000000 : ℝ)^8463 ≤ (3033892676613/25000000000000 : ℝ)^6415 := by
    have hnat : (2021681127 : ℕ)^8463*25000000000000^6415 ≤ 3033892676613^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021681127 10000000000 3033892676613 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415768993/10000000000 : ℝ)^8463 ≤ (44527740841711/100000000000000 : ℝ)^6415 := by
    have hnat : (5415768993 : ℕ)^8463*100000000000000^6415 ≤ 44527740841711^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415768993 10000000000 44527740841711 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305601939/10000000000 : ℝ), (-2021681127/10000000000 : ℝ), (5415768993/10000000000 : ℝ)] ![(21668344219651/50000000000000 : ℝ), (3033892676613/25000000000000 : ℝ), (44527740841711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305601939/10000000000 : ℝ)|^8463 ≤ (21668344219651/50000000000000 : ℝ)^6415
        have hw : |(5305601939/10000000000 : ℝ)|=(5305601939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2021681127/10000000000 : ℝ)|^8463 ≤ (3033892676613/25000000000000 : ℝ)^6415
        have hw : |(-2021681127/10000000000 : ℝ)|=(2021681127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415768993/10000000000 : ℝ)|^8463 ≤ (44527740841711/100000000000000 : ℝ)^6415
        have hw : |(5415768993/10000000000 : ℝ)|=(5415768993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326400447/2500000000 : ℝ)*x 0 + (1353942283/2500000000 : ℝ)*x 1 + (-2021681141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326400447/2500000000 : ℝ)^8463 ≤ (8464196643/19531250000 : ℝ)^6415 := by
    have hnat : (1326400447 : ℕ)^8463*19531250000^6415 ≤ 8464196643^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326400447 2500000000 8464196643 19531250000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353942283/2500000000 : ℝ)^8463 ≤ (8905548469881/20000000000000 : ℝ)^6415 := by
    have hnat : (1353942283 : ℕ)^8463*20000000000000^6415 ≤ 8905548469881^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353942283 2500000000 8905548469881 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021681141/10000000000 : ℝ)^8463 ≤ (12135570817319/100000000000000 : ℝ)^6415 := by
    have hnat : (2021681141 : ℕ)^8463*100000000000000^6415 ≤ 12135570817319^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021681141 10000000000 12135570817319 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326400447/2500000000 : ℝ), (1353942283/2500000000 : ℝ), (-2021681141/10000000000 : ℝ)] ![(8464196643/19531250000 : ℝ), (8905548469881/20000000000000 : ℝ), (12135570817319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326400447/2500000000 : ℝ)|^8463 ≤ (8464196643/19531250000 : ℝ)^6415
        have hw : |(1326400447/2500000000 : ℝ)|=(1326400447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353942283/2500000000 : ℝ)|^8463 ≤ (8905548469881/20000000000000 : ℝ)^6415
        have hw : |(1353942283/2500000000 : ℝ)|=(1353942283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2021681141/10000000000 : ℝ)|^8463 ≤ (12135570817319/100000000000000 : ℝ)^6415
        have hw : |(-2021681141/10000000000 : ℝ)|=(2021681141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s6_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345417113/10000000000 : ℝ)*x 0 + (4525308349/10000000000 : ℝ)*x 1 + (4172489857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345417113/10000000000 : ℝ)^8463 ≤ (16651079211497/50000000000000 : ℝ)^6415 := by
    have hnat : (4345417113 : ℕ)^8463*50000000000000^6415 ≤ 16651079211497^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345417113 10000000000 16651079211497 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525308349/10000000000 : ℝ)^8463 ≤ (35132839640247/100000000000000 : ℝ)^6415 := by
    have hnat : (4525308349 : ℕ)^8463*100000000000000^6415 ≤ 35132839640247^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525308349 10000000000 35132839640247 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172489857/10000000000 : ℝ)^8463 ≤ (31565001922363/100000000000000 : ℝ)^6415 := by
    have hnat : (4172489857 : ℕ)^8463*100000000000000^6415 ≤ 31565001922363^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172489857 10000000000 31565001922363 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345417113/10000000000 : ℝ), (4525308349/10000000000 : ℝ), (4172489857/10000000000 : ℝ)] ![(16651079211497/50000000000000 : ℝ), (35132839640247/100000000000000 : ℝ), (31565001922363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345417113/10000000000 : ℝ)|^8463 ≤ (16651079211497/50000000000000 : ℝ)^6415
        have hw : |(4345417113/10000000000 : ℝ)|=(4345417113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525308349/10000000000 : ℝ)|^8463 ≤ (35132839640247/100000000000000 : ℝ)^6415
        have hw : |(4525308349/10000000000 : ℝ)|=(4525308349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172489857/10000000000 : ℝ)|^8463 ≤ (31565001922363/100000000000000 : ℝ)^6415
        have hw : |(4172489857/10000000000 : ℝ)|=(4172489857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2743/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (733/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10959/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10959/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10959/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10959/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10959/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10959/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10959/100000 : ℝ) ^ (8461/2048 : ℝ) ≤ (10788470279994977/100000000000000000000 : ℝ) := by
    have hpowers : (10959/100000 : ℝ)^8461 ≤ (10788470279994977/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10959 : ℕ)^8461*100000000000000000000^2048 ≤ 10788470279994977^2048*100000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10959 100000 10788470279994977 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10959/100000 : ℝ)) (X := (10788470279994977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7337/50000 : ℝ) ^ (8461/2048 : ℝ) ≤ (36034803632796971/100000000000000000000 : ℝ) := by
    have hpowers : (7337/50000 : ℝ)^8461 ≤ (36034803632796971/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7337 : ℕ)^8461*100000000000000000000^2048 ≤ 36034803632796971^2048*50000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7337 50000 36034803632796971 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7337/50000 : ℝ)) (X := (36034803632796971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010788470279994977/50000000000000000000 : ℝ) ≤ (100005222309573/100000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50010788470279994977/50000000000000000000 : ℝ)^2048 ≤ (100005222309573/100000000000000 : ℝ)^8461 := by
      have hnat : (50010788470279994977 : ℕ)^2048*100000000000000^8461 ≤ 100005222309573^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010788470279994977 50000000000000000000 100005222309573 100000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100005222309573/100000000000000 : ℝ)) (X := (50010788470279994977/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011705818478197987/25000000000000000000 : ℝ) ≤ (1250141645570001/1250000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (25011705818478197987/25000000000000000000 : ℝ)^2048 ≤ (1250141645570001/1250000000000000 : ℝ)^8461 := by
      have hnat : (25011705818478197987 : ℕ)^2048*1250000000000000^8461 ≤ 1250141645570001^8461*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011705818478197987 25000000000000000000 1250141645570001 1250000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250141645570001/1250000000000000 : ℝ)) (X := (25011705818478197987/25000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036034803632796971/50000000000000000000 : ℝ) ≤ (2500436024540679/2500000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50036034803632796971/50000000000000000000 : ℝ)^2048 ≤ (2500436024540679/2500000000000000 : ℝ)^8461 := by
      have hnat : (50036034803632796971 : ℕ)^2048*2500000000000000^8461 ≤ 2500436024540679^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036034803632796971 50000000000000000000 2500436024540679 2500000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500436024540679/2500000000000000 : ℝ)) (X := (50036034803632796971/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10788470279994977/100000000000000000000 : ℝ) ≤ ((9284637411325553889/9287500000000000000 : ℝ)+2*(152733400677/92875000000000 : ℝ)*(10959/100000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (9284637411325553889/9287500000000000000 : ℝ)+2*(152733400677/92875000000000 : ℝ)*(10959/100000 : ℝ)=(100005222309573/100000000000000 : ℝ) by norm_num, show 1+2*(10788470279994977/100000000000000000000 : ℝ)=(50010788470279994977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36034803632796971/100000000000000000000 : ℝ)+(10788470279994977/100000000000000000000 : ℝ) ≤ ((9284637411325553889/9287500000000000000 : ℝ)+(152733400677/92875000000000 : ℝ)*((7337/50000 : ℝ)+(10959/100000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (9284637411325553889/9287500000000000000 : ℝ)+(152733400677/92875000000000 : ℝ)*((7337/50000 : ℝ)+(10959/100000 : ℝ))=(1250141645570001/1250000000000000 : ℝ) by norm_num, show 1+(36034803632796971/100000000000000000000 : ℝ)+(10788470279994977/100000000000000000000 : ℝ)=(25011705818478197987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36034803632796971/100000000000000000000 : ℝ) ≤ ((9284637411325553889/9287500000000000000 : ℝ)+2*(152733400677/92875000000000 : ℝ)*(7337/50000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (9284637411325553889/9287500000000000000 : ℝ)+2*(152733400677/92875000000000 : ℝ)*(7337/50000 : ℝ)=(2500436024540679/2500000000000000 : ℝ) by norm_num, show 1+2*(36034803632796971/100000000000000000000 : ℝ)=(50036034803632796971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9284637411325553889/9287500000000000000 : ℝ)*(X 1 0+X 2 0)+(152733400677/92875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (10959/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9284637411325553889/9287500000000000000 : ℝ)) (alpha := (152733400677/92875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9284637411325553889/9287500000000000000 : ℝ)*(X 0 1+X 2 1)+(152733400677/92875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (10959/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9284637411325553889/9287500000000000000 : ℝ)) (alpha := (152733400677/92875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9284637411325553889/9287500000000000000 : ℝ)*(X 0 2+X 1 2)+(152733400677/92875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (10959/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9284637411325553889/9287500000000000000 : ℝ)) (alpha := (152733400677/92875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526617939/2500000000 : ℝ)*X 0 0+(2708196769/5000000000 : ℝ)*X 0 1+(1310531517/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070020151/2000000000 : ℝ)*X 1 0+(-2195324169/10000000000 : ℝ)*X 1 1+(26210631/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267505037/500000000 : ℝ)*X 2 0+(5242126173/10000000000 : ℝ)*X 2 1+(-1097662113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345390829/10000000000 : ℝ)*X 0 0+(4171217293/10000000000 : ℝ)*X 0 1+(4526574187/10000000000 : ℝ)*X 0 2+(4345390829/10000000000 : ℝ)*X 1 0+(4171217293/10000000000 : ℝ)*X 1 1+(4526574187/10000000000 : ℝ)*X 1 2+(4345390829/10000000000 : ℝ)*X 2 0+(4171217293/10000000000 : ℝ)*X 2 1+(4526574187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1053242349/5000000000 : ℝ)*X 0 0+(1310686837/2500000000 : ℝ)*X 0 1+(2707884557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305601939/10000000000 : ℝ)*X 1 0+(-2021681127/10000000000 : ℝ)*X 1 1+(5415768993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326400447/2500000000 : ℝ)*X 2 0+(1353942283/2500000000 : ℝ)*X 2 1+(-2021681141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345417113/10000000000 : ℝ)*X 0 0+(4525308349/10000000000 : ℝ)*X 0 1+(4172489857/10000000000 : ℝ)*X 0 2+(4345417113/10000000000 : ℝ)*X 1 0+(4525308349/10000000000 : ℝ)*X 1 1+(4172489857/10000000000 : ℝ)*X 1 2+(4345417113/10000000000 : ℝ)*X 2 0+(4525308349/10000000000 : ℝ)*X 2 1+(4172489857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (935173752905913483170278659/116093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1615463417/100000000000000 : ℝ)*(base19) + (1462434389/100000000000000 : ℝ)*(base23) + (73264507/100000000000000 : ℝ)*(lower2) + (5015421/2000000000000 : ℝ)*(upper3) + (19746467/25000000000000 : ℝ)*(upper5) + (2138120541790273/50000000000000 : ℝ)*(major0) + (2138120541790273/50000000000000 : ℝ)*(major1) + (2138120541790273/50000000000000 : ℝ)*(major2) + (5738344336502531/100000000000000 : ℝ)*(sp0) + (5738376905687863/100000000000000 : ℝ)*(sp1) + (1434594264679223/25000000000000 : ℝ)*(sp2) + (1407043152418461/50000000000000 : ℝ)*(sp3) + (27347719/80000000000 : ℝ)*(sp4) + (3414532359/20000000000000 : ℝ)*(sp7) + (2814103377498717/100000000000000 : ℝ)*(f.failure) + (5738378521151281/100000000000000 : ℝ)*(f.sum) + (92722475016293/18575000000000000000000000000 : ℝ)*base65 + (1544090234068996697/464375000000000000000000000000000 : ℝ)*base67 + (5363689282760246697/464375000000000000000000000000000 : ℝ)*base69 + (5782977463420871697/464375000000000000000000000000000 : ℝ)*base71 + (27373746969009/9287500000000000000000000000 : ℝ)*base73 + (9653341739600246697/464375000000000000000000000000000 : ℝ)*base75 + (6846831093642746697/464375000000000000000000000000000 : ℝ)*base77 + (567587575952253303/464375000000000000000000000000000 : ℝ)*base80 + (81284437673793/18575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (33234967/5000000000000000000000 : ℝ)*base90 + (33234967/5000000000000000000000 : ℝ)*base92 + (33234967/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2539806673772685448508278341/464375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (652945863/50000000000000 : ℝ)*(base19) + (152063357/12500000000000 : ℝ)*(base23) + (15462911/12500000000000 : ℝ)*(upper3) + (3122861/12500000000000 : ℝ)*(lower4) + (4306969398244977/100000000000000 : ℝ)*(major0) + (4306969398244977/100000000000000 : ℝ)*(major1) + (4306969398244977/100000000000000 : ℝ)*(major2) + (23324568463/100000000000000 : ℝ)*(sp1) + (1066602851/4000000000000 : ℝ)*(sp2) + (1332283289/50000000000000 : ℝ)*(sp3) + (5779613585845359/100000000000000 : ℝ)*(sp4) + (577958895538517/10000000000000 : ℝ)*(sp5) + (5779585704267227/100000000000000 : ℝ)*(sp6) + (113372894550719/4000000000000 : ℝ)*(sp7) + (354290628541819/12500000000000 : ℝ)*(f.failure) + (5779613585845359/100000000000000 : ℝ)*(f.sum) + (50750075326409/18575000000000000000000000000 : ℝ)*base66 + (2444238405451215553/928750000000000000000000000000000 : ℝ)*base67 + (3350346385053715553/928750000000000000000000000000000 : ℝ)*base69 + (2313644726365034447/928750000000000000000000000000000 : ℝ)*base72 + (3814812840329/4643750000000000000000000000 : ℝ)*base73 + (1099872996961284447/928750000000000000000000000000000 : ℝ)*base76 + (4241555264281215553/928750000000000000000000000000000 : ℝ)*base77 + (4284594045449965553/928750000000000000000000000000000 : ℝ)*base79 + (12702069365229/4643750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4445569/625000000000000000000 : ℝ)*base90 + (4445569/625000000000000000000 : ℝ)*base92 + (4445569/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1269_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (733/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1269_s7_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263310879/1250000000 : ℝ)*x 0 + (1354066763/2500000000 : ℝ)*x 1 + (2621121231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263310879/1250000000 : ℝ)^8463 ≤ (3202902776337/25000000000000 : ℝ)^6415 := by
    have hnat : (263310879 : ℕ)^8463*25000000000000^6415 ≤ 3202902776337^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263310879 1250000000 3202902776337 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354066763/2500000000 : ℝ)^8463 ≤ (11133285806201/25000000000000 : ℝ)^6415 := by
    have hnat : (1354066763 : ℕ)^8463*25000000000000^6415 ≤ 11133285806201^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354066763 2500000000 11133285806201 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621121231/5000000000 : ℝ)^8463 ≤ (42655245652613/100000000000000 : ℝ)^6415 := by
    have hnat : (2621121231 : ℕ)^8463*100000000000000^6415 ≤ 42655245652613^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621121231 5000000000 42655245652613 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263310879/1250000000 : ℝ), (1354066763/2500000000 : ℝ), (2621121231/5000000000 : ℝ)] ![(3202902776337/25000000000000 : ℝ), (11133285806201/25000000000000 : ℝ), (42655245652613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263310879/1250000000 : ℝ)|^8463 ≤ (3202902776337/25000000000000 : ℝ)^6415
        have hw : |(-263310879/1250000000 : ℝ)|=(263310879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354066763/2500000000 : ℝ)|^8463 ≤ (11133285806201/25000000000000 : ℝ)^6415
        have hw : |(1354066763/2500000000 : ℝ)|=(1354066763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621121231/5000000000 : ℝ)|^8463 ≤ (42655245652613/100000000000000 : ℝ)^6415
        have hw : |(2621121231/5000000000 : ℝ)|=(2621121231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337517121/2500000000 : ℝ)*x 0 + (-87808541/400000000 : ℝ)*x 1 + (2621121241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337517121/2500000000 : ℝ)^8463 ≤ (21908244997047/50000000000000 : ℝ)^6415 := by
    have hnat : (1337517121 : ℕ)^8463*50000000000000^6415 ≤ 21908244997047^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337517121 2500000000 21908244997047 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87808541/400000000 : ℝ)^8463 ≤ (2705652824177/20000000000000 : ℝ)^6415 := by
    have hnat : (87808541 : ℕ)^8463*20000000000000^6415 ≤ 2705652824177^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87808541 400000000 2705652824177 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621121241/5000000000 : ℝ)^8463 ≤ (5331905733413/12500000000000 : ℝ)^6415 := by
    have hnat : (2621121241 : ℕ)^8463*12500000000000^6415 ≤ 5331905733413^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621121241 5000000000 5331905733413 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337517121/2500000000 : ℝ), (-87808541/400000000 : ℝ), (2621121241/5000000000 : ℝ)] ![(21908244997047/50000000000000 : ℝ), (2705652824177/20000000000000 : ℝ), (5331905733413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337517121/2500000000 : ℝ)|^8463 ≤ (21908244997047/50000000000000 : ℝ)^6415
        have hw : |(1337517121/2500000000 : ℝ)|=(1337517121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87808541/400000000 : ℝ)|^8463 ≤ (2705652824177/20000000000000 : ℝ)^6415
        have hw : |(-87808541/400000000 : ℝ)|=(87808541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621121241/5000000000 : ℝ)|^8463 ≤ (5331905733413/12500000000000 : ℝ)^6415
        have hw : |(2621121241/5000000000 : ℝ)|=(2621121241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675034287/5000000000 : ℝ)*x 0 + (5242242291/10000000000 : ℝ)*x 1 + (-2195213659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675034287/5000000000 : ℝ)^8463 ≤ (43816490966501/100000000000000 : ℝ)^6415 := by
    have hnat : (2675034287 : ℕ)^8463*100000000000000^6415 ≤ 43816490966501^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675034287 5000000000 43816490966501 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242242291/10000000000 : ℝ)^8463 ≤ (2665952738563/6250000000000 : ℝ)^6415 := by
    have hnat : (5242242291 : ℕ)^8463*6250000000000^6415 ≤ 2665952738563^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242242291 10000000000 2665952738563 6250000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195213659/10000000000 : ℝ)^8463 ≤ (13528265210311/100000000000000 : ℝ)^6415 := by
    have hnat : (2195213659 : ℕ)^8463*100000000000000^6415 ≤ 13528265210311^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195213659 10000000000 13528265210311 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675034287/5000000000 : ℝ), (5242242291/10000000000 : ℝ), (-2195213659/10000000000 : ℝ)] ![(43816490966501/100000000000000 : ℝ), (2665952738563/6250000000000 : ℝ), (13528265210311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675034287/5000000000 : ℝ)|^8463 ≤ (43816490966501/100000000000000 : ℝ)^6415
        have hw : |(2675034287/5000000000 : ℝ)|=(2675034287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242242291/10000000000 : ℝ)|^8463 ≤ (2665952738563/6250000000000 : ℝ)^6415
        have hw : |(5242242291/10000000000 : ℝ)|=(5242242291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195213659/10000000000 : ℝ)|^8463 ≤ (13528265210311/100000000000000 : ℝ)^6415
        have hw : |(-2195213659/10000000000 : ℝ)|=(2195213659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271587453/625000000 : ℝ)*x 0 + (166858543/400000000 : ℝ)*x 1 + (4526325937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271587453/625000000 : ℝ)^8463 ≤ (33301977800711/100000000000000 : ℝ)^6415 := by
    have hnat : (271587453 : ℕ)^8463*100000000000000^6415 ≤ 33301977800711^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271587453 625000000 33301977800711 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166858543/400000000 : ℝ)^8463 ≤ (31554759849293/100000000000000 : ℝ)^6415 := by
    have hnat : (166858543 : ℕ)^8463*100000000000000^6415 ≤ 31554759849293^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166858543 400000000 31554759849293 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526325937/10000000000 : ℝ)^8463 ≤ (17571631171129/50000000000000 : ℝ)^6415 := by
    have hnat : (4526325937 : ℕ)^8463*50000000000000^6415 ≤ 17571631171129^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526325937 10000000000 17571631171129 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271587453/625000000 : ℝ), (166858543/400000000 : ℝ), (4526325937/10000000000 : ℝ)] ![(33301977800711/100000000000000 : ℝ), (31554759849293/100000000000000 : ℝ), (17571631171129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271587453/625000000 : ℝ)|^8463 ≤ (33301977800711/100000000000000 : ℝ)^6415
        have hw : |(271587453/625000000 : ℝ)|=(271587453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166858543/400000000 : ℝ)|^8463 ≤ (31554759849293/100000000000000 : ℝ)^6415
        have hw : |(166858543/400000000 : ℝ)|=(166858543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526325937/10000000000 : ℝ)|^8463 ≤ (17571631171129/50000000000000 : ℝ)^6415
        have hw : |(4526325937/10000000000 : ℝ)|=(4526325937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263312517/1250000000 : ℝ)*x 0 + (5242861483/10000000000 : ℝ)*x 1 + (1083128947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263312517/1250000000 : ℝ)^8463 ≤ (12811716247523/100000000000000 : ℝ)^6415 := by
    have hnat : (263312517 : ℕ)^8463*100000000000000^6415 ≤ 12811716247523^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263312517 1250000000 12811716247523 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242861483/10000000000 : ℝ)^8463 ≤ (42661890677197/100000000000000 : ℝ)^6415 := by
    have hnat : (5242861483 : ℕ)^8463*100000000000000^6415 ≤ 42661890677197^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242861483 10000000000 42661890677197 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083128947/2000000000 : ℝ)^8463 ≤ (22263196527797/50000000000000 : ℝ)^6415 := by
    have hnat : (1083128947 : ℕ)^8463*50000000000000^6415 ≤ 22263196527797^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083128947 2000000000 22263196527797 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263312517/1250000000 : ℝ), (5242861483/10000000000 : ℝ), (1083128947/2000000000 : ℝ)] ![(12811716247523/100000000000000 : ℝ), (42661890677197/100000000000000 : ℝ), (22263196527797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263312517/1250000000 : ℝ)|^8463 ≤ (12811716247523/100000000000000 : ℝ)^6415
        have hw : |(-263312517/1250000000 : ℝ)|=(263312517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242861483/10000000000 : ℝ)|^8463 ≤ (42661890677197/100000000000000 : ℝ)^6415
        have hw : |(5242861483/10000000000 : ℝ)|=(5242861483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083128947/2000000000 : ℝ)|^8463 ≤ (22263196527797/50000000000000 : ℝ)^6415
        have hw : |(1083128947/2000000000 : ℝ)|=(1083128947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305631643/10000000000 : ℝ)*x 0 + (-505452679/2500000000 : ℝ)*x 1 + (5415644869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305631643/10000000000 : ℝ)^8463 ≤ (21668504261687/50000000000000 : ℝ)^6415 := by
    have hnat : (5305631643 : ℕ)^8463*50000000000000^6415 ≤ 21668504261687^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305631643 10000000000 21668504261687 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505452679/2500000000 : ℝ)^8463 ≤ (12136596943787/100000000000000 : ℝ)^6415 := by
    have hnat : (505452679 : ℕ)^8463*100000000000000^6415 ≤ 12136596943787^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505452679 2500000000 12136596943787 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415644869/10000000000 : ℝ)^8463 ≤ (44526394509043/100000000000000 : ℝ)^6415 := by
    have hnat : (5415644869 : ℕ)^8463*100000000000000^6415 ≤ 44526394509043^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415644869 10000000000 44526394509043 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305631643/10000000000 : ℝ), (-505452679/2500000000 : ℝ), (5415644869/10000000000 : ℝ)] ![(21668504261687/50000000000000 : ℝ), (12136596943787/100000000000000 : ℝ), (44526394509043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305631643/10000000000 : ℝ)|^8463 ≤ (21668504261687/50000000000000 : ℝ)^6415
        have hw : |(5305631643/10000000000 : ℝ)|=(5305631643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505452679/2500000000 : ℝ)|^8463 ≤ (12136596943787/100000000000000 : ℝ)^6415
        have hw : |(-505452679/2500000000 : ℝ)|=(505452679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415644869/10000000000 : ℝ)|^8463 ≤ (44526394509043/100000000000000 : ℝ)^6415
        have hw : |(5415644869/10000000000 : ℝ)|=(5415644869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061126277/2000000000 : ℝ)*x 0 + (1083128971/2000000000 : ℝ)*x 1 + (-126363193/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061126277/2000000000 : ℝ)^8463 ≤ (21668502871609/50000000000000 : ℝ)^6415 := by
    have hnat : (1061126277 : ℕ)^8463*50000000000000^6415 ≤ 21668502871609^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061126277 2000000000 21668502871609 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083128971/2000000000 : ℝ)^8463 ≤ (4452639435719/10000000000000 : ℝ)^6415 := by
    have hnat : (1083128971 : ℕ)^8463*10000000000000^6415 ≤ 4452639435719^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083128971 2000000000 4452639435719 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126363193/625000000 : ℝ)^8463 ≤ (12136599889749/100000000000000 : ℝ)^6415 := by
    have hnat : (126363193 : ℕ)^8463*100000000000000^6415 ≤ 12136599889749^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126363193 625000000 12136599889749 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061126277/2000000000 : ℝ), (1083128971/2000000000 : ℝ), (-126363193/625000000 : ℝ)] ![(21668502871609/50000000000000 : ℝ), (4452639435719/10000000000000 : ℝ), (12136599889749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061126277/2000000000 : ℝ)|^8463 ≤ (21668502871609/50000000000000 : ℝ)^6415
        have hw : |(1061126277/2000000000 : ℝ)|=(1061126277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083128971/2000000000 : ℝ)|^8463 ≤ (4452639435719/10000000000000 : ℝ)^6415
        have hw : |(1083128971/2000000000 : ℝ)|=(1083128971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126363193/625000000 : ℝ)|^8463 ≤ (12136599889749/100000000000000 : ℝ)^6415
        have hw : |(-126363193/625000000 : ℝ)|=(126363193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_s7_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345425951/10000000000 : ℝ)*x 0 + (4525062843/10000000000 : ℝ)*x 1 + (4172732851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345425951/10000000000 : ℝ)^8463 ≤ (3330224777879/10000000000000 : ℝ)^6415 := by
    have hnat : (4345425951 : ℕ)^8463*10000000000000^6415 ≤ 3330224777879^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345425951 10000000000 3330224777879 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525062843/10000000000 : ℝ)^8463 ≤ (17565162571669/50000000000000 : ℝ)^6415 := by
    have hnat : (4525062843 : ℕ)^8463*50000000000000^6415 ≤ 17565162571669^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525062843 10000000000 17565162571669 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172732851/10000000000 : ℝ)^8463 ≤ (31567427067853/100000000000000 : ℝ)^6415 := by
    have hnat : (4172732851 : ℕ)^8463*100000000000000^6415 ≤ 31567427067853^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172732851 10000000000 31567427067853 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345425951/10000000000 : ℝ), (4525062843/10000000000 : ℝ), (4172732851/10000000000 : ℝ)] ![(3330224777879/10000000000000 : ℝ), (17565162571669/50000000000000 : ℝ), (31567427067853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345425951/10000000000 : ℝ)|^8463 ≤ (3330224777879/10000000000000 : ℝ)^6415
        have hw : |(4345425951/10000000000 : ℝ)|=(4345425951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525062843/10000000000 : ℝ)|^8463 ≤ (17565162571669/50000000000000 : ℝ)^6415
        have hw : |(4525062843/10000000000 : ℝ)|=(4525062843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172732851/10000000000 : ℝ)|^8463 ≤ (31567427067853/100000000000000 : ℝ)^6415
        have hw : |(4172732851/10000000000 : ℝ)|=(4172732851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (439/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14657/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (733/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (733/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (733/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (733/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (733/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (733/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2743/25000 : ℝ) ^ (8461/2048 : ℝ) ≤ (542072017628187/5000000000000000000 : ℝ) := by
    have hpowers : (2743/25000 : ℝ)^8461 ≤ (542072017628187/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2743 : ℕ)^8461*5000000000000000000^2048 ≤ 542072017628187^2048*25000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2743 25000 542072017628187 5000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2743/25000 : ℝ)) (X := (542072017628187/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (733/5000 : ℝ) ^ (8461/2048 : ℝ) ≤ (7178596258542817/20000000000000000000 : ℝ) := by
    have hpowers : (733/5000 : ℝ)^8461 ≤ (7178596258542817/20000000000000000000 : ℝ)^2048 := by
      have hnat : (733 : ℕ)^8461*20000000000000000000^2048 ≤ 7178596258542817^2048*5000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        733 5000 7178596258542817 20000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (733/5000 : ℝ)) (X := (7178596258542817/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500542072017628187/2500000000000000000 : ℝ) ≤ (10000524794836911/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (2500542072017628187/2500000000000000000 : ℝ)^2048 ≤ (10000524794836911/10000000000000000 : ℝ)^8461 := by
      have hnat : (2500542072017628187 : ℕ)^2048*10000000000000000^8461 ≤ 10000524794836911^8461*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500542072017628187 2500000000000000000 10000524794836911 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000524794836911/10000000000000000 : ℝ)) (X := (2500542072017628187/2500000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001869376865811113/4000000000000000000 : ℝ) ≤ (2000226202927481/2000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (4001869376865811113/4000000000000000000 : ℝ)^2048 ≤ (2000226202927481/2000000000000000 : ℝ)^8461 := by
      have hnat : (4001869376865811113 : ℕ)^2048*2000000000000000^8461 ≤ 2000226202927481^8461*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001869376865811113 4000000000000000000 2000226202927481 2000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000226202927481/2000000000000000 : ℝ)) (X := (4001869376865811113/4000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007178596258542817/10000000000000000000 : ℝ) ≤ (10001737234437899/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (10007178596258542817/10000000000000000000 : ℝ)^2048 ≤ (10001737234437899/10000000000000000 : ℝ)^8461 := by
      have hnat : (10007178596258542817 : ℕ)^2048*10000000000000000^8461 ≤ 10001737234437899^8461*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007178596258542817 10000000000000000000 10001737234437899 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001737234437899/10000000000000000 : ℝ)) (X := (10007178596258542817/10000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(542072017628187/5000000000000000000 : ℝ) ≤ ((4608579069507060929/4610000000000000000 : ℝ)+2*(303109900247/184400000000000 : ℝ)*(2743/25000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (4608579069507060929/4610000000000000000 : ℝ)+2*(303109900247/184400000000000 : ℝ)*(2743/25000 : ℝ)=(10000524794836911/10000000000000000 : ℝ) by norm_num, show 1+2*(542072017628187/5000000000000000000 : ℝ)=(2500542072017628187/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7178596258542817/20000000000000000000 : ℝ)+(542072017628187/5000000000000000000 : ℝ) ≤ ((4608579069507060929/4610000000000000000 : ℝ)+(303109900247/184400000000000 : ℝ)*((733/5000 : ℝ)+(2743/25000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (4608579069507060929/4610000000000000000 : ℝ)+(303109900247/184400000000000 : ℝ)*((733/5000 : ℝ)+(2743/25000 : ℝ))=(2000226202927481/2000000000000000 : ℝ) by norm_num, show 1+(7178596258542817/20000000000000000000 : ℝ)+(542072017628187/5000000000000000000 : ℝ)=(4001869376865811113/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7178596258542817/20000000000000000000 : ℝ) ≤ ((4608579069507060929/4610000000000000000 : ℝ)+2*(303109900247/184400000000000 : ℝ)*(733/5000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (4608579069507060929/4610000000000000000 : ℝ)+2*(303109900247/184400000000000 : ℝ)*(733/5000 : ℝ)=(10001737234437899/10000000000000000 : ℝ) by norm_num, show 1+2*(7178596258542817/20000000000000000000 : ℝ)=(10007178596258542817/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4608579069507060929/4610000000000000000 : ℝ)*(X 1 0+X 2 0)+(303109900247/184400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (733/5000 : ℝ)) (c := (4608579069507060929/4610000000000000000 : ℝ)) (alpha := (303109900247/184400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4608579069507060929/4610000000000000000 : ℝ)*(X 0 1+X 2 1)+(303109900247/184400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (733/5000 : ℝ)) (c := (4608579069507060929/4610000000000000000 : ℝ)) (alpha := (303109900247/184400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4608579069507060929/4610000000000000000 : ℝ)*(X 0 2+X 1 2)+(303109900247/184400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (733/5000 : ℝ)) (c := (4608579069507060929/4610000000000000000 : ℝ)) (alpha := (303109900247/184400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263310879/1250000000 : ℝ)*X 0 0+(1354066763/2500000000 : ℝ)*X 0 1+(2621121231/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337517121/2500000000 : ℝ)*X 1 0+(-87808541/400000000 : ℝ)*X 1 1+(2621121241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675034287/5000000000 : ℝ)*X 2 0+(5242242291/10000000000 : ℝ)*X 2 1+(-2195213659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271587453/625000000 : ℝ)*X 0 0+(166858543/400000000 : ℝ)*X 0 1+(4526325937/10000000000 : ℝ)*X 0 2+(271587453/625000000 : ℝ)*X 1 0+(166858543/400000000 : ℝ)*X 1 1+(4526325937/10000000000 : ℝ)*X 1 2+(271587453/625000000 : ℝ)*X 2 0+(166858543/400000000 : ℝ)*X 2 1+(4526325937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263312517/1250000000 : ℝ)*X 0 0+(5242861483/10000000000 : ℝ)*X 0 1+(1083128947/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305631643/10000000000 : ℝ)*X 1 0+(-505452679/2500000000 : ℝ)*X 1 1+(5415644869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061126277/2000000000 : ℝ)*X 2 0+(1083128971/2000000000 : ℝ)*X 2 1+(-126363193/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345425951/10000000000 : ℝ)*X 0 0+(4525062843/10000000000 : ℝ)*X 0 1+(4172732851/10000000000 : ℝ)*X 0 2+(4345425951/10000000000 : ℝ)*X 1 0+(4525062843/10000000000 : ℝ)*X 1 1+(4172732851/10000000000 : ℝ)*X 1 2+(4345425951/10000000000 : ℝ)*X 2 0+(4525062843/10000000000 : ℝ)*X 2 1+(4172732851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (481594505440438305440392803/115250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159304483/50000000000000 : ℝ)*(base19) + (415068973/100000000000000 : ℝ)*(base23) + (5061749/100000000000000 : ℝ)*(upper2) + (93819617/100000000000000 : ℝ)*(upper3) + (2141081426301569/50000000000000 : ℝ)*(major0) + (2141081426301569/50000000000000 : ℝ)*(major1) + (2141081426301569/50000000000000 : ℝ)*(major2) + (5746321203925503/100000000000000 : ℝ)*(sp0) + (718290609933217/12500000000000 : ℝ)*(sp1) + (718290452392051/12500000000000 : ℝ)*(sp2) + (1408998170037341/50000000000000 : ℝ)*(sp3) + (9985373/250000000000 : ℝ)*(sp4) + (1163869321/100000000000000 : ℝ)*(sp6) + (100694177/2500000000000 : ℝ)*(sp7) + (1409000183920881/50000000000000 : ℝ)*(f.failure) + (2873162599037351/50000000000000 : ℝ)*(f.sum) + (1171372916343/4610000000000000000000000000 : ℝ)*base65 + (817810926046872601/230500000000000000000000000000000 : ℝ)*base67 + (1969334026950127399/230500000000000000000000000000000 : ℝ)*base70 + (1308226360120127399/230500000000000000000000000000000 : ℝ)*base72 + (13186078141643/4610000000000000000000000000 : ℝ)*base73 + (2173482495686872601/230500000000000000000000000000000 : ℝ)*base75 + (401166806086627399/230500000000000000000000000000000 : ℝ)*base78 + (1967720128876627399/230500000000000000000000000000000 : ℝ)*base80 + (21256646224797/4610000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3357869/2500000000000000000000 : ℝ)*base89 + (3357869/2500000000000000000000 : ℝ)*base91 + (3357869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32748486360339356638389987/23050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928773611/100000000000000 : ℝ)*(base19) + (555561781/100000000000000 : ℝ)*(base23) + (121789737/50000000000000 : ℝ)*(lower1) + (465481/1562500000000 : ℝ)*(upper2) + (80971189/50000000000000 : ℝ)*(upper5) + (431291427898133/10000000000000 : ℝ)*(major0) + (431291427898133/10000000000000 : ℝ)*(major1) + (431291427898133/10000000000000 : ℝ)*(major2) + (8380533/312500000000 : ℝ)*(sp0) + (17661785041/100000000000000 : ℝ)*(sp1) + (5787588600828223/100000000000000 : ℝ)*(sp4) + (578757269204013/10000000000000 : ℝ)*(sp5) + (5787590727037001/100000000000000 : ℝ)*(sp6) + (22173728343791/781250000000 : ℝ)*(sp7) + (22173728343791/781250000000 : ℝ)*(f.failure) + (5787591282598783/100000000000000 : ℝ)*(f.sum) + (3662939157651/922000000000000000000000000 : ℝ)*base65 + (167618387840320557/46100000000000000000000000000000 : ℝ)*base67 + (164047814682320557/46100000000000000000000000000000 : ℝ)*base69 + (182400427107420557/46100000000000000000000000000000 : ℝ)*base71 + (2449932698347/922000000000000000000000000 : ℝ)*base74 + (1014314826749620557/46100000000000000000000000000000 : ℝ)*base75 + (478763729866320557/46100000000000000000000000000000 : ℝ)*base77 + (331611945041720557/46100000000000000000000000000000 : ℝ)*base79 + (1684716494269/922000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (66209/39062500000000000000 : ℝ)*base89 + (66209/39062500000000000000 : ℝ)*base91 + (66209/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1269_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14657/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1269_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1269_box_0 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-966697341/5000000000 : ℝ)*x 0 + (5392851891/10000000000 : ℝ)*x 1 + (215714029/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966697341/5000000000 : ℝ)^8463 ≤ (2288269066327/20000000000000 : ℝ)^6415 := by
    have hnat : (966697341 : ℕ)^8463*20000000000000^6415 ≤ 2288269066327^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966697341 5000000000 2288269066327 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392851891/10000000000 : ℝ)^8463 ≤ (44279333644009/100000000000000 : ℝ)^6415 := by
    have hnat : (5392851891 : ℕ)^8463*100000000000000^6415 ≤ 44279333644009^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392851891 10000000000 44279333644009 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215714029/400000000 : ℝ)^8463 ≤ (44279321013851/100000000000000 : ℝ)^6415 := by
    have hnat : (215714029 : ℕ)^8463*100000000000000^6415 ≤ 44279321013851^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215714029 400000000 44279321013851 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966697341/5000000000 : ℝ), (5392851891/10000000000 : ℝ), (215714029/400000000 : ℝ)] ![(2288269066327/20000000000000 : ℝ), (44279333644009/100000000000000 : ℝ), (44279321013851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966697341/5000000000 : ℝ)|^8463 ≤ (2288269066327/20000000000000 : ℝ)^6415
        have hw : |(-966697341/5000000000 : ℝ)|=(966697341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392851891/10000000000 : ℝ)|^8463 ≤ (44279333644009/100000000000000 : ℝ)^6415
        have hw : |(5392851891/10000000000 : ℝ)|=(5392851891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215714029/400000000 : ℝ)|^8463 ≤ (44279321013851/100000000000000 : ℝ)^6415
        have hw : |(215714029/400000000 : ℝ)|=(215714029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_1 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660497139/1250000000 : ℝ)*x 0 + (-2082168911/10000000000 : ℝ)*x 1 + (1348212957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660497139/1250000000 : ℝ)^8463 ≤ (43103815797591/100000000000000 : ℝ)^6415 := by
    have hnat : (660497139 : ℕ)^8463*100000000000000^6415 ≤ 43103815797591^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660497139 1250000000 43103815797591 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082168911/10000000000 : ℝ)^8463 ≤ (6308425613953/50000000000000 : ℝ)^6415 := by
    have hnat : (2082168911 : ℕ)^8463*50000000000000^6415 ≤ 6308425613953^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082168911 10000000000 6308425613953 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348212957/2500000000 : ℝ)^8463 ≤ (44279332961591/100000000000000 : ℝ)^6415 := by
    have hnat : (1348212957 : ℕ)^8463*100000000000000^6415 ≤ 44279332961591^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348212957 2500000000 44279332961591 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660497139/1250000000 : ℝ), (-2082168911/10000000000 : ℝ), (1348212957/2500000000 : ℝ)] ![(43103815797591/100000000000000 : ℝ), (6308425613953/50000000000000 : ℝ), (44279332961591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660497139/1250000000 : ℝ)|^8463 ≤ (43103815797591/100000000000000 : ℝ)^6415
        have hw : |(660497139/1250000000 : ℝ)|=(660497139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082168911/10000000000 : ℝ)|^8463 ≤ (6308425613953/50000000000000 : ℝ)^6415
        have hw : |(-2082168911/10000000000 : ℝ)|=(2082168911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348212957/2500000000 : ℝ)|^8463 ≤ (44279332961591/100000000000000 : ℝ)^6415
        have hw : |(1348212957/2500000000 : ℝ)|=(1348212957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_2 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641988677/5000000000 : ℝ)*x 0 + (5392852237/10000000000 : ℝ)*x 1 + (-208216803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641988677/5000000000 : ℝ)^8463 ≤ (43103818401931/100000000000000 : ℝ)^6415 := by
    have hnat : (2641988677 : ℕ)^8463*100000000000000^6415 ≤ 43103818401931^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641988677 5000000000 43103818401931 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392852237/10000000000 : ℝ)^8463 ≤ (8855867478379/20000000000000 : ℝ)^6415 := by
    have hnat : (5392852237 : ℕ)^8463*20000000000000^6415 ≤ 8855867478379^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392852237 10000000000 8855867478379 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208216803/1000000000 : ℝ)^8463 ≤ (98569095197/781250000000 : ℝ)^6415 := by
    have hnat : (208216803 : ℕ)^8463*781250000000^6415 ≤ 98569095197^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208216803 1000000000 98569095197 781250000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641988677/5000000000 : ℝ), (5392852237/10000000000 : ℝ), (-208216803/1000000000 : ℝ)] ![(43103818401931/100000000000000 : ℝ), (8855867478379/20000000000000 : ℝ), (98569095197/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641988677/5000000000 : ℝ)|^8463 ≤ (43103818401931/100000000000000 : ℝ)^6415
        have hw : |(2641988677/5000000000 : ℝ)|=(2641988677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392852237/10000000000 : ℝ)|^8463 ≤ (8855867478379/20000000000000 : ℝ)^6415
        have hw : |(5392852237/10000000000 : ℝ)|=(5392852237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208216803/1000000000 : ℝ)|^8463 ≤ (98569095197/781250000000 : ℝ)^6415
        have hw : |(-208216803/1000000000 : ℝ)|=(208216803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_3 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2247683563/5000000000 : ℝ)*x 0 + (4274471361/10000000000 : ℝ)*x 1 + (854894487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2247683563/5000000000 : ℝ)^8463 ≤ (3482650036553/10000000000000 : ℝ)^6415 := by
    have hnat : (2247683563 : ℕ)^8463*10000000000000^6415 ≤ 3482650036553^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247683563 5000000000 3482650036553 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4274471361/10000000000 : ℝ)^8463 ≤ (1018335762707/3125000000000 : ℝ)^6415 := by
    have hnat : (4274471361 : ℕ)^8463*3125000000000^6415 ≤ 1018335762707^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274471361 10000000000 1018335762707 3125000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (854894487/2000000000 : ℝ)^8463 ≤ (6517351041657/20000000000000 : ℝ)^6415 := by
    have hnat : (854894487 : ℕ)^8463*20000000000000^6415 ≤ 6517351041657^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854894487 2000000000 6517351041657 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2247683563/5000000000 : ℝ), (4274471361/10000000000 : ℝ), (854894487/2000000000 : ℝ)] ![(3482650036553/10000000000000 : ℝ), (1018335762707/3125000000000 : ℝ), (6517351041657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2247683563/5000000000 : ℝ)|^8463 ≤ (3482650036553/10000000000000 : ℝ)^6415
        have hw : |(2247683563/5000000000 : ℝ)|=(2247683563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4274471361/10000000000 : ℝ)|^8463 ≤ (1018335762707/3125000000000 : ℝ)^6415
        have hw : |(4274471361/10000000000 : ℝ)|=(4274471361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(854894487/2000000000 : ℝ)|^8463 ≤ (6517351041657/20000000000000 : ℝ)^6415
        have hw : |(854894487/2000000000 : ℝ)|=(854894487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_4 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-456469249/2000000000 : ℝ)*x 0 + (5263115537/10000000000 : ℝ)*x 1 + (2631557451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456469249/2000000000 : ℝ)^8463 ≤ (14241105648801/100000000000000 : ℝ)^6415 := by
    have hnat : (456469249 : ℕ)^8463*100000000000000^6415 ≤ 14241105648801^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456469249 2000000000 14241105648801 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263115537/10000000000 : ℝ)^8463 ≤ (42879450579111/100000000000000 : ℝ)^6415 := by
    have hnat : (5263115537 : ℕ)^8463*100000000000000^6415 ≤ 42879450579111^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263115537 10000000000 42879450579111 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631557451/5000000000 : ℝ)^8463 ≤ (42879443754031/100000000000000 : ℝ)^6415 := by
    have hnat : (2631557451 : ℕ)^8463*100000000000000^6415 ≤ 42879443754031^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631557451 5000000000 42879443754031 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456469249/2000000000 : ℝ), (5263115537/10000000000 : ℝ), (2631557451/5000000000 : ℝ)] ![(14241105648801/100000000000000 : ℝ), (42879450579111/100000000000000 : ℝ), (42879443754031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456469249/2000000000 : ℝ)|^8463 ≤ (14241105648801/100000000000000 : ℝ)^6415
        have hw : |(-456469249/2000000000 : ℝ)|=(456469249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263115537/10000000000 : ℝ)|^8463 ≤ (42879450579111/100000000000000 : ℝ)^6415
        have hw : |(5263115537/10000000000 : ℝ)|=(5263115537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631557451/5000000000 : ℝ)|^8463 ≤ (42879443754031/100000000000000 : ℝ)^6415
        have hw : |(2631557451/5000000000 : ℝ)|=(2631557451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_5 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687688831/5000000000 : ℝ)*x 0 + (-1066849597/5000000000 : ℝ)*x 1 + (5263115361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687688831/5000000000 : ℝ)^8463 ≤ (44090150066717/100000000000000 : ℝ)^6415 := by
    have hnat : (2687688831 : ℕ)^8463*100000000000000^6415 ≤ 44090150066717^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687688831 5000000000 44090150066717 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066849597/5000000000 : ℝ)^8463 ≤ (13030401227983/100000000000000 : ℝ)^6415 := by
    have hnat : (1066849597 : ℕ)^8463*100000000000000^6415 ≤ 13030401227983^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066849597 5000000000 13030401227983 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263115361/10000000000 : ℝ)^8463 ≤ (8575889737487/20000000000000 : ℝ)^6415 := by
    have hnat : (5263115361 : ℕ)^8463*20000000000000^6415 ≤ 8575889737487^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263115361 10000000000 8575889737487 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687688831/5000000000 : ℝ), (-1066849597/5000000000 : ℝ), (5263115361/10000000000 : ℝ)] ![(44090150066717/100000000000000 : ℝ), (13030401227983/100000000000000 : ℝ), (8575889737487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687688831/5000000000 : ℝ)|^8463 ≤ (44090150066717/100000000000000 : ℝ)^6415
        have hw : |(2687688831/5000000000 : ℝ)|=(2687688831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066849597/5000000000 : ℝ)|^8463 ≤ (13030401227983/100000000000000 : ℝ)^6415
        have hw : |(-1066849597/5000000000 : ℝ)|=(1066849597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263115361/10000000000 : ℝ)|^8463 ≤ (8575889737487/20000000000000 : ℝ)^6415
        have hw : |(5263115361/10000000000 : ℝ)|=(5263115361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_6 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687688461/5000000000 : ℝ)*x 0 + (2631557957/5000000000 : ℝ)*x 1 + (-42673989/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687688461/5000000000 : ℝ)^8463 ≤ (11022535514827/25000000000000 : ℝ)^6415 := by
    have hnat : (2687688461 : ℕ)^8463*25000000000000^6415 ≤ 11022535514827^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687688461 5000000000 11022535514827 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631557957/5000000000 : ℝ)^8463 ≤ (21439727315583/50000000000000 : ℝ)^6415 := by
    have hnat : (2631557957 : ℕ)^8463*50000000000000^6415 ≤ 21439727315583^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631557957 5000000000 21439727315583 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42673989/200000000 : ℝ)^8463 ≤ (521216131619/4000000000000 : ℝ)^6415 := by
    have hnat : (42673989 : ℕ)^8463*4000000000000^6415 ≤ 521216131619^6415*200000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42673989 200000000 521216131619 4000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687688461/5000000000 : ℝ), (2631557957/5000000000 : ℝ), (-42673989/200000000 : ℝ)] ![(11022535514827/25000000000000 : ℝ), (21439727315583/50000000000000 : ℝ), (521216131619/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687688461/5000000000 : ℝ)|^8463 ≤ (11022535514827/25000000000000 : ℝ)^6415
        have hw : |(2687688461/5000000000 : ℝ)|=(2687688461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631557957/5000000000 : ℝ)|^8463 ≤ (21439727315583/50000000000000 : ℝ)^6415
        have hw : |(2631557957/5000000000 : ℝ)|=(2631557957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42673989/200000000 : ℝ)|^8463 ≤ (521216131619/4000000000000 : ℝ)^6415
        have hw : |(-42673989/200000000 : ℝ)|=(42673989/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_7 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2097307331/5000000000 : ℝ)*x 0 + (4424791801/10000000000 : ℝ)*x 1 + (2212396089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097307331/5000000000 : ℝ)^8463 ≤ (15892999024703/50000000000000 : ℝ)^6415 := by
    have hnat : (2097307331 : ℕ)^8463*50000000000000^6415 ≤ 15892999024703^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097307331 5000000000 15892999024703 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4424791801/10000000000 : ℝ)^8463 ≤ (3410699905197/10000000000000 : ℝ)^6415 := by
    have hnat : (4424791801 : ℕ)^8463*10000000000000^6415 ≤ 3410699905197^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424791801 10000000000 3410699905197 10000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212396089/5000000000 : ℝ)^8463 ≤ (8526750721421/25000000000000 : ℝ)^6415 := by
    have hnat : (2212396089 : ℕ)^8463*25000000000000^6415 ≤ 8526750721421^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212396089 5000000000 8526750721421 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097307331/5000000000 : ℝ), (4424791801/10000000000 : ℝ), (2212396089/5000000000 : ℝ)] ![(15892999024703/50000000000000 : ℝ), (3410699905197/10000000000000 : ℝ), (8526750721421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097307331/5000000000 : ℝ)|^8463 ≤ (15892999024703/50000000000000 : ℝ)^6415
        have hw : |(2097307331/5000000000 : ℝ)|=(2097307331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4424791801/10000000000 : ℝ)|^8463 ≤ (3410699905197/10000000000000 : ℝ)^6415
        have hw : |(4424791801/10000000000 : ℝ)|=(4424791801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212396089/5000000000 : ℝ)|^8463 ≤ (8526750721421/25000000000000 : ℝ)^6415
        have hw : |(2212396089/5000000000 : ℝ)|=(2212396089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_8 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-34519869/156250000 : ℝ)*x 0 + (5174148739/10000000000 : ℝ)*x 1 + (540689521/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34519869/156250000 : ℝ)^8463 ≤ (3410668426979/25000000000000 : ℝ)^6415 := by
    have hnat : (34519869 : ℕ)^8463*25000000000000^6415 ≤ 3410668426979^6415*156250000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34519869 156250000 3410668426979 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174148739/10000000000 : ℝ)^8463 ≤ (41925811645237/100000000000000 : ℝ)^6415 := by
    have hnat : (5174148739 : ℕ)^8463*100000000000000^6415 ≤ 41925811645237^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174148739 10000000000 41925811645237 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540689521/1000000000 : ℝ)^8463 ≤ (22215757317261/50000000000000 : ℝ)^6415 := by
    have hnat : (540689521 : ℕ)^8463*50000000000000^6415 ≤ 22215757317261^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540689521 1000000000 22215757317261 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34519869/156250000 : ℝ), (5174148739/10000000000 : ℝ), (540689521/1000000000 : ℝ)] ![(3410668426979/25000000000000 : ℝ), (41925811645237/100000000000000 : ℝ), (22215757317261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34519869/156250000 : ℝ)|^8463 ≤ (3410668426979/25000000000000 : ℝ)^6415
        have hw : |(-34519869/156250000 : ℝ)|=(34519869/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174148739/10000000000 : ℝ)|^8463 ≤ (41925811645237/100000000000000 : ℝ)^6415
        have hw : |(5174148739/10000000000 : ℝ)|=(5174148739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540689521/1000000000 : ℝ)|^8463 ≤ (22215757317261/50000000000000 : ℝ)^6415
        have hw : |(540689521/1000000000 : ℝ)|=(540689521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_9 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (210963077/400000000 : ℝ)*x 0 + (-259556691/1250000000 : ℝ)*x 1 + (108137901/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210963077/400000000 : ℝ)^8463 ≤ (42997304443649/100000000000000 : ℝ)^6415 := by
    have hnat : (210963077 : ℕ)^8463*100000000000000^6415 ≤ 42997304443649^6415*400000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210963077 400000000 42997304443649 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259556691/1250000000 : ℝ)^8463 ≤ (12571182639037/100000000000000 : ℝ)^6415 := by
    have hnat : (259556691 : ℕ)^8463*100000000000000^6415 ≤ 12571182639037^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259556691 1250000000 12571182639037 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108137901/200000000 : ℝ)^8463 ≤ (11107878224989/25000000000000 : ℝ)^6415 := by
    have hnat : (108137901 : ℕ)^8463*25000000000000^6415 ≤ 11107878224989^6415*200000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108137901 200000000 11107878224989 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210963077/400000000 : ℝ), (-259556691/1250000000 : ℝ), (108137901/200000000 : ℝ)] ![(42997304443649/100000000000000 : ℝ), (12571182639037/100000000000000 : ℝ), (11107878224989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210963077/400000000 : ℝ)|^8463 ≤ (42997304443649/100000000000000 : ℝ)^6415
        have hw : |(210963077/400000000 : ℝ)|=(210963077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259556691/1250000000 : ℝ)|^8463 ≤ (12571182639037/100000000000000 : ℝ)^6415
        have hw : |(-259556691/1250000000 : ℝ)|=(259556691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108137901/200000000 : ℝ)|^8463 ≤ (11107878224989/25000000000000 : ℝ)^6415
        have hw : |(108137901/200000000 : ℝ)|=(108137901/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_10 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2637038431/5000000000 : ℝ)*x 0 + (1081379009/2000000000 : ℝ)*x 1 + (-103822681/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637038431/5000000000 : ℝ)^8463 ≤ (8599460753213/20000000000000 : ℝ)^6415 := by
    have hnat : (2637038431 : ℕ)^8463*20000000000000^6415 ≤ 8599460753213^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637038431 5000000000 8599460753213 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081379009/2000000000 : ℝ)^8463 ≤ (44431512845751/100000000000000 : ℝ)^6415 := by
    have hnat : (1081379009 : ℕ)^8463*100000000000000^6415 ≤ 44431512845751^6415*2000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081379009 2000000000 44431512845751 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103822681/500000000 : ℝ)^8463 ≤ (6285591686919/50000000000000 : ℝ)^6415 := by
    have hnat : (103822681 : ℕ)^8463*50000000000000^6415 ≤ 6285591686919^6415*500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103822681 500000000 6285591686919 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637038431/5000000000 : ℝ), (1081379009/2000000000 : ℝ), (-103822681/500000000 : ℝ)] ![(8599460753213/20000000000000 : ℝ), (44431512845751/100000000000000 : ℝ), (6285591686919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637038431/5000000000 : ℝ)|^8463 ≤ (8599460753213/20000000000000 : ℝ)^6415
        have hw : |(2637038431/5000000000 : ℝ)|=(2637038431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081379009/2000000000 : ℝ)|^8463 ≤ (44431512845751/100000000000000 : ℝ)^6415
        have hw : |(1081379009/2000000000 : ℝ)|=(1081379009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103822681/500000000 : ℝ)|^8463 ≤ (6285591686919/50000000000000 : ℝ)^6415
        have hw : |(-103822681/500000000 : ℝ)|=(103822681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_11 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4527362037/10000000000 : ℝ)*x 0 + (4258186577/10000000000 : ℝ)*x 1 + (425818677/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4527362037/10000000000 : ℝ)^8463 ≤ (17576937711547/50000000000000 : ℝ)^6415 := by
    have hnat : (4527362037 : ℕ)^8463*50000000000000^6415 ≤ 17576937711547^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527362037 10000000000 17576937711547 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4258186577/10000000000 : ℝ)^8463 ≤ (16211530656499/50000000000000 : ℝ)^6415 := by
    have hnat : (4258186577 : ℕ)^8463*50000000000000^6415 ≤ 16211530656499^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258186577 10000000000 16211530656499 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425818677/1000000000 : ℝ)^8463 ≤ (16211531625857/50000000000000 : ℝ)^6415 := by
    have hnat : (425818677 : ℕ)^8463*50000000000000^6415 ≤ 16211531625857^6415*1000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425818677 1000000000 16211531625857 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4527362037/10000000000 : ℝ), (4258186577/10000000000 : ℝ), (425818677/1000000000 : ℝ)] ![(17576937711547/50000000000000 : ℝ), (16211530656499/50000000000000 : ℝ), (16211531625857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4527362037/10000000000 : ℝ)|^8463 ≤ (17576937711547/50000000000000 : ℝ)^6415
        have hw : |(4527362037/10000000000 : ℝ)|=(4527362037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4258186577/10000000000 : ℝ)|^8463 ≤ (16211530656499/50000000000000 : ℝ)^6415
        have hw : |(4258186577/10000000000 : ℝ)|=(4258186577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425818677/1000000000 : ℝ)|^8463 ≤ (16211531625857/50000000000000 : ℝ)^6415
        have hw : |(425818677/1000000000 : ℝ)|=(425818677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_12 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2006951579/10000000000 : ℝ)*x 0 + (342465167/625000000 : ℝ)*x 1 + (656514371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006951579/10000000000 : ℝ)^8463 ≤ (480762479459/4000000000000 : ℝ)^6415 := by
    have hnat : (2006951579 : ℕ)^8463*4000000000000^6415 ≤ 480762479459^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006951579 10000000000 480762479459 4000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342465167/625000000 : ℝ)^8463 ≤ (45219683787369/100000000000000 : ℝ)^6415 := by
    have hnat : (342465167 : ℕ)^8463*100000000000000^6415 ≤ 45219683787369^6415*625000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342465167 625000000 45219683787369 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656514371/1250000000 : ℝ)^8463 ≤ (10690313551679/25000000000000 : ℝ)^6415 := by
    have hnat : (656514371 : ℕ)^8463*25000000000000^6415 ≤ 10690313551679^6415*1250000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656514371 1250000000 10690313551679 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2006951579/10000000000 : ℝ), (342465167/625000000 : ℝ), (656514371/1250000000 : ℝ)] ![(480762479459/4000000000000 : ℝ), (45219683787369/100000000000000 : ℝ), (10690313551679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2006951579/10000000000 : ℝ)|^8463 ≤ (480762479459/4000000000000 : ℝ)^6415
        have hw : |(-2006951579/10000000000 : ℝ)|=(2006951579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342465167/625000000 : ℝ)|^8463 ≤ (45219683787369/100000000000000 : ℝ)^6415
        have hw : |(342465167/625000000 : ℝ)|=(342465167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656514371/1250000000 : ℝ)|^8463 ≤ (10690313551679/25000000000000 : ℝ)^6415
        have hw : |(656514371/1250000000 : ℝ)|=(656514371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_13 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26915619/50000000 : ℝ)*x 0 + (-2137961941/10000000000 : ℝ)*x 1 + (5252115097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26915619/50000000 : ℝ)^8463 ≤ (5521748615741/12500000000000 : ℝ)^6415 := by
    have hnat : (26915619 : ℕ)^8463*12500000000000^6415 ≤ 5521748615741^6415*50000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26915619 50000000 5521748615741 12500000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2137961941/10000000000 : ℝ)^8463 ≤ (2612951092031/20000000000000 : ℝ)^6415 := by
    have hnat : (2137961941 : ℕ)^8463*20000000000000^6415 ≤ 2612951092031^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137961941 10000000000 2612951092031 20000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252115097/10000000000 : ℝ)^8463 ≤ (21380627796151/50000000000000 : ℝ)^6415 := by
    have hnat : (5252115097 : ℕ)^8463*50000000000000^6415 ≤ 21380627796151^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252115097 10000000000 21380627796151 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26915619/50000000 : ℝ), (-2137961941/10000000000 : ℝ), (5252115097/10000000000 : ℝ)] ![(5521748615741/12500000000000 : ℝ), (2612951092031/20000000000000 : ℝ), (21380627796151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26915619/50000000 : ℝ)|^8463 ≤ (5521748615741/12500000000000 : ℝ)^6415
        have hw : |(26915619/50000000 : ℝ)|=(26915619/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2137961941/10000000000 : ℝ)|^8463 ≤ (2612951092031/20000000000000 : ℝ)^6415
        have hw : |(-2137961941/10000000000 : ℝ)|=(2137961941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252115097/10000000000 : ℝ)|^8463 ≤ (21380627796151/50000000000000 : ℝ)^6415
        have hw : |(5252115097/10000000000 : ℝ)|=(5252115097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_14 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5383124319/10000000000 : ℝ)*x 0 + (5252114509/10000000000 : ℝ)*x 1 + (-534490507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383124319/10000000000 : ℝ)^8463 ≤ (22086997272259/50000000000000 : ℝ)^6415 := by
    have hnat : (5383124319 : ℕ)^8463*50000000000000^6415 ≤ 22086997272259^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383124319 10000000000 22086997272259 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252114509/10000000000 : ℝ)^8463 ≤ (21380624638303/50000000000000 : ℝ)^6415 := by
    have hnat : (5252114509 : ℕ)^8463*50000000000000^6415 ≤ 21380624638303^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252114509 10000000000 21380624638303 50000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534490507/2500000000 : ℝ)^8463 ≤ (13064756161527/100000000000000 : ℝ)^6415 := by
    have hnat : (534490507 : ℕ)^8463*100000000000000^6415 ≤ 13064756161527^6415*2500000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534490507 2500000000 13064756161527 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383124319/10000000000 : ℝ), (5252114509/10000000000 : ℝ), (-534490507/2500000000 : ℝ)] ![(22086997272259/50000000000000 : ℝ), (21380624638303/50000000000000 : ℝ), (13064756161527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383124319/10000000000 : ℝ)|^8463 ≤ (22086997272259/50000000000000 : ℝ)^6415
        have hw : |(5383124319/10000000000 : ℝ)|=(5383124319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252114509/10000000000 : ℝ)|^8463 ≤ (21380624638303/50000000000000 : ℝ)^6415
        have hw : |(5252114509/10000000000 : ℝ)|=(5252114509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534490507/2500000000 : ℝ)|^8463 ≤ (13064756161527/100000000000000 : ℝ)^6415
        have hw : |(-534490507/2500000000 : ℝ)|=(534490507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1269_box_15 (p : ℝ) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2084333311/5000000000 : ℝ)*x 0 + (4437528081/10000000000 : ℝ)*x 1 + (2218764113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084333311/5000000000 : ℝ)^8463 ≤ (31526850945359/100000000000000 : ℝ)^6415 := by
    have hnat : (2084333311 : ℕ)^8463*100000000000000^6415 ≤ 31526850945359^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084333311 5000000000 31526850945359 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4437528081/10000000000 : ℝ)^8463 ≤ (34236573782473/100000000000000 : ℝ)^6415 := by
    have hnat : (4437528081 : ℕ)^8463*100000000000000^6415 ≤ 34236573782473^6415*10000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437528081 10000000000 34236573782473 100000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218764113/5000000000 : ℝ)^8463 ≤ (8559143814583/25000000000000 : ℝ)^6415 := by
    have hnat : (2218764113 : ℕ)^8463*25000000000000^6415 ≤ 8559143814583^6415*5000000000^8463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218764113 5000000000 8559143814583 25000000000000 8463 6415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8463/2048 : ℝ)) 8463 6415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084333311/5000000000 : ℝ), (4437528081/10000000000 : ℝ), (2218764113/5000000000 : ℝ)] ![(31526850945359/100000000000000 : ℝ), (34236573782473/100000000000000 : ℝ), (8559143814583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084333311/5000000000 : ℝ)|^8463 ≤ (31526850945359/100000000000000 : ℝ)^6415
        have hw : |(2084333311/5000000000 : ℝ)|=(2084333311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4437528081/10000000000 : ℝ)|^8463 ≤ (34236573782473/100000000000000 : ℝ)^6415
        have hw : |(4437528081/10000000000 : ℝ)|=(4437528081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2218764113/5000000000 : ℝ)|^8463 ≤ (8559143814583/25000000000000 : ℝ)^6415
        have hw : |(2218764113/5000000000 : ℝ)|=(2218764113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1269_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12567/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29403/50000 : ℝ) ∧ (79531/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84073/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (439/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (439/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (439/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (439/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (439/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (439/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (439/4000 : ℝ) ^ (8461/2048 : ℝ) ≤ (5426846079085011/50000000000000000000 : ℝ) := by
    have hpowers : (439/4000 : ℝ)^8461 ≤ (5426846079085011/50000000000000000000 : ℝ)^2048 := by
      have hnat : (439 : ℕ)^8461*50000000000000000000^2048 ≤ 5426846079085011^2048*4000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 4000 5426846079085011 50000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/4000 : ℝ)) (X := (5426846079085011/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14657/100000 : ℝ) ^ (8461/2048 : ℝ) ≤ (35862645914708837/100000000000000000000 : ℝ) := by
    have hpowers : (14657/100000 : ℝ)^8461 ≤ (35862645914708837/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14657 : ℕ)^8461*100000000000000000000^2048 ≤ 35862645914708837^2048*100000^8461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14657 100000 35862645914708837 100000000000000000000 8461 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14657/100000 : ℝ)) (X := (35862645914708837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005426846079085011/25000000000000000000 : ℝ) ≤ (10000525387853639/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (25005426846079085011/25000000000000000000 : ℝ)^2048 ≤ (10000525387853639/10000000000000000 : ℝ)^8461 := by
      have hnat : (25005426846079085011 : ℕ)^2048*10000000000000000^8461 ≤ 10000525387853639^8461*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005426846079085011 25000000000000000000 10000525387853639 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000525387853639/10000000000000000 : ℝ)) (X := (25005426846079085011/25000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046716338072878859/100000000000000000000 : ℝ) ≤ (2000226115415259/2000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (100046716338072878859/100000000000000000000 : ℝ)^2048 ≤ (2000226115415259/2000000000000000 : ℝ)^8461 := by
      have hnat : (100046716338072878859 : ℕ)^2048*2000000000000000^8461 ≤ 2000226115415259^8461*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046716338072878859 100000000000000000000 2000226115415259 2000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000226115415259/2000000000000000 : ℝ)) (X := (100046716338072878859/100000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035862645914708837/50000000000000000000 : ℝ) ≤ (10001735766298951/10000000000000000 : ℝ) ^ (8461/2048 : ℝ) := by
    have hpowers : (50035862645914708837/50000000000000000000 : ℝ)^2048 ≤ (10001735766298951/10000000000000000 : ℝ)^8461 := by
      have hnat : (50035862645914708837 : ℕ)^2048*10000000000000000^8461 ≤ 10001735766298951^8461*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035862645914708837 50000000000000000000 10001735766298951 10000000000000000 2048 8461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001735766298951/10000000000000000 : ℝ)) (X := (50035862645914708837/50000000000000000000 : ℝ)) (by norm_num) 8461 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5426846079085011/50000000000000000000 : ℝ) ≤ ((18404325287319899799/18410000000000000000 : ℝ)+2*(2364020401/1438281250000 : ℝ)*(439/4000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (18404325287319899799/18410000000000000000 : ℝ)+2*(2364020401/1438281250000 : ℝ)*(439/4000 : ℝ)=(10000525387853639/10000000000000000 : ℝ) by norm_num, show 1+2*(5426846079085011/50000000000000000000 : ℝ)=(25005426846079085011/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35862645914708837/100000000000000000000 : ℝ)+(5426846079085011/50000000000000000000 : ℝ) ≤ ((18404325287319899799/18410000000000000000 : ℝ)+(2364020401/1438281250000 : ℝ)*((14657/100000 : ℝ)+(439/4000 : ℝ)))^(8461/2048 : ℝ) := by
    rw [show (18404325287319899799/18410000000000000000 : ℝ)+(2364020401/1438281250000 : ℝ)*((14657/100000 : ℝ)+(439/4000 : ℝ))=(2000226115415259/2000000000000000 : ℝ) by norm_num, show 1+(35862645914708837/100000000000000000000 : ℝ)+(5426846079085011/50000000000000000000 : ℝ)=(100046716338072878859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35862645914708837/100000000000000000000 : ℝ) ≤ ((18404325287319899799/18410000000000000000 : ℝ)+2*(2364020401/1438281250000 : ℝ)*(14657/100000 : ℝ))^(8461/2048 : ℝ) := by
    rw [show (18404325287319899799/18410000000000000000 : ℝ)+2*(2364020401/1438281250000 : ℝ)*(14657/100000 : ℝ)=(10001735766298951/10000000000000000 : ℝ) by norm_num, show 1+2*(35862645914708837/100000000000000000000 : ℝ)=(50035862645914708837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18404325287319899799/18410000000000000000 : ℝ)*(X 1 0+X 2 0)+(2364020401/1438281250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (439/4000 : ℝ)) (hi := (14657/100000 : ℝ)) (c := (18404325287319899799/18410000000000000000 : ℝ)) (alpha := (2364020401/1438281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18404325287319899799/18410000000000000000 : ℝ)*(X 0 1+X 2 1)+(2364020401/1438281250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (439/4000 : ℝ)) (hi := (14657/100000 : ℝ)) (c := (18404325287319899799/18410000000000000000 : ℝ)) (alpha := (2364020401/1438281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18404325287319899799/18410000000000000000 : ℝ)*(X 0 2+X 1 2)+(2364020401/1438281250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8461/2048 : ℝ)) (lo := (439/4000 : ℝ)) (hi := (14657/100000 : ℝ)) (c := (18404325287319899799/18410000000000000000 : ℝ)) (alpha := (2364020401/1438281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-966697341/5000000000 : ℝ)*X 0 0+(5392851891/10000000000 : ℝ)*X 0 1+(215714029/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660497139/1250000000 : ℝ)*X 1 0+(-2082168911/10000000000 : ℝ)*X 1 1+(1348212957/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2641988677/5000000000 : ℝ)*X 2 0+(5392852237/10000000000 : ℝ)*X 2 1+(-208216803/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2247683563/5000000000 : ℝ)*X 0 0+(4274471361/10000000000 : ℝ)*X 0 1+(854894487/2000000000 : ℝ)*X 0 2+(2247683563/5000000000 : ℝ)*X 1 0+(4274471361/10000000000 : ℝ)*X 1 1+(854894487/2000000000 : ℝ)*X 1 2+(2247683563/5000000000 : ℝ)*X 2 0+(4274471361/10000000000 : ℝ)*X 2 1+(854894487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-456469249/2000000000 : ℝ)*X 0 0+(5263115537/10000000000 : ℝ)*X 0 1+(2631557451/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687688831/5000000000 : ℝ)*X 1 0+(-1066849597/5000000000 : ℝ)*X 1 1+(5263115361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2687688461/5000000000 : ℝ)*X 2 0+(2631557957/5000000000 : ℝ)*X 2 1+(-42673989/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097307331/5000000000 : ℝ)*X 0 0+(4424791801/10000000000 : ℝ)*X 0 1+(2212396089/5000000000 : ℝ)*X 0 2+(2097307331/5000000000 : ℝ)*X 1 0+(4424791801/10000000000 : ℝ)*X 1 1+(2212396089/5000000000 : ℝ)*X 1 2+(2097307331/5000000000 : ℝ)*X 2 0+(4424791801/10000000000 : ℝ)*X 2 1+(2212396089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-34519869/156250000 : ℝ)*X 0 0+(5174148739/10000000000 : ℝ)*X 0 1+(540689521/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((210963077/400000000 : ℝ)*X 1 0+(-259556691/1250000000 : ℝ)*X 1 1+(108137901/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637038431/5000000000 : ℝ)*X 2 0+(1081379009/2000000000 : ℝ)*X 2 1+(-103822681/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4527362037/10000000000 : ℝ)*X 0 0+(4258186577/10000000000 : ℝ)*X 0 1+(425818677/1000000000 : ℝ)*X 0 2+(4527362037/10000000000 : ℝ)*X 1 0+(4258186577/10000000000 : ℝ)*X 1 1+(425818677/1000000000 : ℝ)*X 1 2+(4527362037/10000000000 : ℝ)*X 2 0+(4258186577/10000000000 : ℝ)*X 2 1+(425818677/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2006951579/10000000000 : ℝ)*X 0 0+(342465167/625000000 : ℝ)*X 0 1+(656514371/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((26915619/50000000 : ℝ)*X 1 0+(-2137961941/10000000000 : ℝ)*X 1 1+(5252115097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5383124319/10000000000 : ℝ)*X 2 0+(5252114509/10000000000 : ℝ)*X 2 1+(-534490507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2084333311/5000000000 : ℝ)*X 0 0+(4437528081/10000000000 : ℝ)*X 0 1+(2218764113/5000000000 : ℝ)*X 0 2+(2084333311/5000000000 : ℝ)*X 1 0+(4437528081/10000000000 : ℝ)*X 1 1+(2218764113/5000000000 : ℝ)*X 1 2+(2084333311/5000000000 : ℝ)*X 2 0+(4437528081/10000000000 : ℝ)*X 2 1+(2218764113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1269_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12567/20000 : ℝ) ≤ (-28918574801149966987963458274203/46025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1488373/3125000000000 : ℝ)*(upper0) + (18419247/100000000000000 : ℝ)*(upper2) + (26625851/20000000000000 : ℝ)*(upper3) + (32008473/20000000000000 : ℝ)*(lower4) + (142027895748799/5000000000000 : ℝ)*(major0) + (142027895748799/5000000000000 : ℝ)*(major1) + (142027895748799/5000000000000 : ℝ)*(major2) + (2648136283/100000000000000 : ℝ)*(sp3) + (1916374570290393/50000000000000 : ℝ)*(sp4) + (1916355118970881/50000000000000 : ℝ)*(sp5) + (1916287252998489/50000000000000 : ℝ)*(sp6) + (934654073777373/50000000000000 : ℝ)*(sp7) + (2431414939/6250000000000 : ℝ)*(sp13) + (174634583809/100000000000000 : ℝ)*(sp14) + (1869310795691029/100000000000000 : ℝ)*(f.failure) + (1916374570290393/50000000000000 : ℝ)*(f.sum) + (2338270855187/460250000000000000000000000 : ℝ)*base65 + (76611216207177343/13150000000000000000000000000000 : ℝ)*base67 + (123601320034077343/13150000000000000000000000000000 : ℝ)*base69 + (3257763083727343/13150000000000000000000000000000 : ℝ)*base71 + (6228660910511/1841000000000000000000000000 : ℝ)*base73 + (45150018574377343/13150000000000000000000000000000 : ℝ)*base75 + (17776991946722657/13150000000000000000000000000000 : ℝ)*base78 + (25601374564472657/13150000000000000000000000000000 : ℝ)*base80 + (12833495391707/1841000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26057279/5000000000000000000000 : ℝ)*base90 + (26057279/5000000000000000000000 : ℝ)*base92 + (26057279/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29403/50000 : ℝ) ≤ (270667068802873411117610326683537/460250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (506530947/100000000000000 : ℝ)*(lower1) + (439940699/100000000000000 : ℝ)*(lower2) + (77518129/50000000000000 : ℝ)*(lower5) + (1453467783288207/50000000000000 : ℝ)*(major0) + (1453467783288207/50000000000000 : ℝ)*(major1) + (1453467783288207/50000000000000 : ℝ)*(major2) + (1940635207316421/50000000000000 : ℝ)*(sp0) + (970303641957543/25000000000000 : ℝ)*(sp1) + (3881244479557533/100000000000000 : ℝ)*(sp2) + (478247526908671/25000000000000 : ℝ)*(sp3) + (6246819803/20000000000000 : ℝ)*(sp6) + (1204951151/50000000000000 : ℝ)*(sp7) + (2649511853/50000000000000 : ℝ)*(sp8) + (7643228297/12500000000000 : ℝ)*(sp9) + (956496258768493/50000000000000 : ℝ)*(f.failure) + (970318928414137/25000000000000 : ℝ)*(f.sum) + (9635894382831/1150625000000000000000000000 : ℝ)*base66 + (89571866780432801/131500000000000000000000000000000 : ℝ)*base68 + (614291875236432801/131500000000000000000000000000000 : ℝ)*base70 + (561186805565432801/131500000000000000000000000000000 : ℝ)*base72 + (37965627237281/4602500000000000000000000000 : ℝ)*base73 + (269924212775432801/131500000000000000000000000000000 : ℝ)*base76 + (1210407887477432801/131500000000000000000000000000000 : ℝ)*base78 + (816249424142932801/131500000000000000000000000000000 : ℝ)*base80 + (3770759603703/2301250000000000000000000000 : ℝ)*base81 + (28755257/2500000000000000000000 : ℝ)*base89 + (28755257/2500000000000000000000 : ℝ)*base91 + (28755257/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79531/100000 : ℝ) ≤ (104586819145549592748822091474371/131500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2625331/25000000000000 : ℝ)*(upper2) + (138387/312500000000 : ℝ)*(lower3) + (628617/1250000000000 : ℝ)*(lower4) + (23426603/100000000000000 : ℝ)*(lower5) + (3221527162979867/100000000000000 : ℝ)*(major0) + (3221527162979867/100000000000000 : ℝ)*(major1) + (3221527162979867/100000000000000 : ℝ)*(major2) + (34062565977/100000000000000 : ℝ)*(sp1) + (1913564463/20000000000000 : ℝ)*(sp3) + (2514091493/50000000000000 : ℝ)*(sp4) + (17186078008633/400000000000 : ℝ)*(sp8) + (4296490467775259/100000000000000 : ℝ)*(sp9) + (1074131132585309/25000000000000 : ℝ)*(sp10) + (2120008993538749/100000000000000 : ℝ)*(sp11) + (265002320170133/12500000000000 : ℝ)*(f.failure) + (1074131132585309/25000000000000 : ℝ)*(f.sum) + (20811694210627/1315000000000000000000000000 : ℝ)*base66 + (804083284555436181/263000000000000000000000000000000 : ℝ)*base68 + (1816182109896436181/263000000000000000000000000000000 : ℝ)*base70 + (845324914721436181/263000000000000000000000000000000 : ℝ)*base72 + (4021668032267/1315000000000000000000000000 : ℝ)*base74 + (1197654510838436181/263000000000000000000000000000000 : ℝ)*base76 + (6556728760600436181/263000000000000000000000000000000 : ℝ)*base78 + (166564811599436181/263000000000000000000000000000000 : ℝ)*base80 + (2127172887743/1315000000000000000000000000 : ℝ)*base81 + (3753617/625000000000000000000 : ℝ)*base89 + (3753617/625000000000000000000 : ℝ)*base91 + (3753617/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84073/100000 : ℝ) ≤ (-193466770149648027548225025693633/230125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60704807/100000000000000 : ℝ)*(upper1) + (19633433/12500000000000 : ℝ)*(upper3) + (84048449/25000000000000 : ℝ)*(upper5) + (814303346076337/25000000000000 : ℝ)*(major0) + (814303346076337/25000000000000 : ℝ)*(major1) + (814303346076337/25000000000000 : ℝ)*(major2) + (4763722733/25000000000000 : ℝ)*(sp4) + (1101364369/2000000000000 : ℝ)*(sp5) + (174872906629/50000000000000 : ℝ)*(sp6) + (1047766387/625000000000 : ℝ)*(sp7) + (68733253761407/1562500000000 : ℝ)*(sp12) + (439889222740253/10000000000000 : ℝ)*(sp13) + (2199298774903861/50000000000000 : ℝ)*(sp14) + (1071667631291053/50000000000000 : ℝ)*(sp15) + (85740116208161/4000000000000 : ℝ)*(f.failure) + (219947364781049/5000000000000 : ℝ)*(f.sum) + (303550156243/1150625000000000000000000000 : ℝ)*base65 + (54026257967563391/65750000000000000000000000000000 : ℝ)*base68 + (618100610036063391/65750000000000000000000000000000 : ℝ)*base70 + (411063198377063391/65750000000000000000000000000000 : ℝ)*base72 + (4924634394859/2301250000000000000000000000 : ℝ)*base74 + (2555462411665063391/65750000000000000000000000000000 : ℝ)*base76 + (513471801457563391/65750000000000000000000000000000 : ℝ)*base78 + (477128005695063391/65750000000000000000000000000000 : ℝ)*base80 + (89698586523107/1150625000000000000000000000 : ℝ)*base82 + (370589/200000000000000000000 : ℝ)*base89 + (370589/200000000000000000000 : ℝ)*base91 + (370589/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1269_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12567/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29403/50000 : ℝ) else (79531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84073/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1269_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1269_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12567/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29403/50000 : ℝ) else (79531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84073/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1269_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1269_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1269_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8461/2048 : ℝ) ≤ p) (hpb : p ≤ (8463/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75978749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10959/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12567/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29403/50000 : ℝ) else (79531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84073/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1269_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

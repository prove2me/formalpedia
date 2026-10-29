-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1664_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:59.957099+00:00
-- url     : https://prove2.me/submissions/502b6586-0503-4745-8161-76a01b431b5f

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
theorem support_rectangle_w1664_s0_0 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91775231/625000000 : ℝ)*x 0 + (721027531/1250000000 : ℝ)*x 1 + (493090587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91775231/625000000 : ℝ)^4975 ≤ (178625200247/2000000000000 : ℝ)^3951 := by
    have hnat : (91775231 : ℕ)^4975*2000000000000^3951 ≤ 178625200247^3951*625000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91775231 625000000 178625200247 2000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721027531/1250000000 : ℝ)^4975 ≤ (50016106133791/100000000000000 : ℝ)^3951 := by
    have hnat : (721027531 : ℕ)^4975*100000000000000^3951 ≤ 50016106133791^3951*1250000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721027531 1250000000 50016106133791 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493090587/1000000000 : ℝ)^4975 ≤ (41052633837803/100000000000000 : ℝ)^3951 := by
    have hnat : (493090587 : ℕ)^4975*100000000000000^3951 ≤ 41052633837803^3951*1000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493090587 1000000000 41052633837803 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91775231/625000000 : ℝ), (721027531/1250000000 : ℝ), (493090587/1000000000 : ℝ)] ![(178625200247/2000000000000 : ℝ), (50016106133791/100000000000000 : ℝ), (41052633837803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91775231/625000000 : ℝ)|^4975 ≤ (178625200247/2000000000000 : ℝ)^3951
        have hw : |(-91775231/625000000 : ℝ)|=(91775231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721027531/1250000000 : ℝ)|^4975 ≤ (50016106133791/100000000000000 : ℝ)^3951
        have hw : |(721027531/1250000000 : ℝ)|=(721027531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(493090587/1000000000 : ℝ)|^4975 ≤ (41052633837803/100000000000000 : ℝ)^3951
        have hw : |(493090587/1000000000 : ℝ)|=(493090587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_1 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2716013013/5000000000 : ℝ)*x 0 + (-1926735177/10000000000 : ℝ)*x 1 + (2465453329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716013013/5000000000 : ℝ)^4975 ≤ (46373578041547/100000000000000 : ℝ)^3951 := by
    have hnat : (2716013013 : ℕ)^4975*100000000000000^3951 ≤ 46373578041547^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716013013 5000000000 46373578041547 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926735177/10000000000 : ℝ)^4975 ≤ (12573779849523/100000000000000 : ℝ)^3951 := by
    have hnat : (1926735177 : ℕ)^4975*100000000000000^3951 ≤ 12573779849523^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926735177 10000000000 12573779849523 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2465453329/5000000000 : ℝ)^4975 ≤ (41052642098689/100000000000000 : ℝ)^3951 := by
    have hnat : (2465453329 : ℕ)^4975*100000000000000^3951 ≤ 41052642098689^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465453329 5000000000 41052642098689 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716013013/5000000000 : ℝ), (-1926735177/10000000000 : ℝ), (2465453329/5000000000 : ℝ)] ![(46373578041547/100000000000000 : ℝ), (12573779849523/100000000000000 : ℝ), (41052642098689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716013013/5000000000 : ℝ)|^4975 ≤ (46373578041547/100000000000000 : ℝ)^3951
        have hw : |(2716013013/5000000000 : ℝ)|=(2716013013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1926735177/10000000000 : ℝ)|^4975 ≤ (12573779849523/100000000000000 : ℝ)^3951
        have hw : |(-1926735177/10000000000 : ℝ)|=(1926735177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2465453329/5000000000 : ℝ)|^4975 ≤ (41052642098689/100000000000000 : ℝ)^3951
        have hw : |(2465453329/5000000000 : ℝ)|=(2465453329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_2 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5432027753/10000000000 : ℝ)*x 0 + (1232726383/2500000000 : ℝ)*x 1 + (-1926734353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5432027753/10000000000 : ℝ)^4975 ≤ (23186798303107/50000000000000 : ℝ)^3951 := by
    have hnat : (5432027753 : ℕ)^4975*50000000000000^3951 ≤ 23186798303107^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432027753 10000000000 23186798303107 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232726383/2500000000 : ℝ)^4975 ≤ (41052630294429/100000000000000 : ℝ)^3951 := by
    have hnat : (1232726383 : ℕ)^4975*100000000000000^3951 ≤ 41052630294429^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232726383 2500000000 41052630294429 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926734353/10000000000 : ℝ)^4975 ≤ (1571721634807/12500000000000 : ℝ)^3951 := by
    have hnat : (1926734353 : ℕ)^4975*12500000000000^3951 ≤ 1571721634807^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926734353 10000000000 1571721634807 12500000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5432027753/10000000000 : ℝ), (1232726383/2500000000 : ℝ), (-1926734353/10000000000 : ℝ)] ![(23186798303107/50000000000000 : ℝ), (41052630294429/100000000000000 : ℝ), (1571721634807/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5432027753/10000000000 : ℝ)|^4975 ≤ (23186798303107/50000000000000 : ℝ)^3951
        have hw : |(5432027753/10000000000 : ℝ)|=(5432027753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232726383/2500000000 : ℝ)|^4975 ≤ (41052630294429/100000000000000 : ℝ)^3951
        have hw : |(1232726383/2500000000 : ℝ)|=(1232726383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926734353/10000000000 : ℝ)|^4975 ≤ (1571721634807/12500000000000 : ℝ)^3951
        have hw : |(-1926734353/10000000000 : ℝ)|=(1926734353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_3 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2042055399/5000000000 : ℝ)*x 0 + (771568133/2500000000 : ℝ)*x 1 + (5290869583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042055399/5000000000 : ℝ)^4975 ≤ (32382006527779/100000000000000 : ℝ)^3951 := by
    have hnat : (2042055399 : ℕ)^4975*100000000000000^3951 ≤ 32382006527779^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042055399 5000000000 32382006527779 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771568133/2500000000 : ℝ)^4975 ≤ (11378328309937/50000000000000 : ℝ)^3951 := by
    have hnat : (771568133 : ℕ)^4975*50000000000000^3951 ≤ 11378328309937^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771568133 2500000000 11378328309937 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5290869583/10000000000 : ℝ)^4975 ≤ (22430668421031/50000000000000 : ℝ)^3951 := by
    have hnat : (5290869583 : ℕ)^4975*50000000000000^3951 ≤ 22430668421031^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290869583 10000000000 22430668421031 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042055399/5000000000 : ℝ), (771568133/2500000000 : ℝ), (5290869583/10000000000 : ℝ)] ![(32382006527779/100000000000000 : ℝ), (11378328309937/50000000000000 : ℝ), (22430668421031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042055399/5000000000 : ℝ)|^4975 ≤ (32382006527779/100000000000000 : ℝ)^3951
        have hw : |(2042055399/5000000000 : ℝ)|=(2042055399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771568133/2500000000 : ℝ)|^4975 ≤ (11378328309937/50000000000000 : ℝ)^3951
        have hw : |(771568133/2500000000 : ℝ)|=(771568133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5290869583/10000000000 : ℝ)|^4975 ≤ (22430668421031/50000000000000 : ℝ)^3951
        have hw : |(5290869583/10000000000 : ℝ)|=(5290869583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_4 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-735273851/5000000000 : ℝ)*x 0 + (4951517871/10000000000 : ℝ)*x 1 + (229876167/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735273851/5000000000 : ℝ)^4975 ≤ (1789536670223/20000000000000 : ℝ)^3951 := by
    have hnat : (735273851 : ℕ)^4975*20000000000000^3951 ≤ 1789536670223^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735273851 5000000000 1789536670223 20000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4951517871/10000000000 : ℝ)^4975 ≤ (41268833730413/100000000000000 : ℝ)^3951 := by
    have hnat : (4951517871 : ℕ)^4975*100000000000000^3951 ≤ 41268833730413^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4951517871 10000000000 41268833730413 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229876167/400000000 : ℝ)^4975 ≤ (24891741451863/50000000000000 : ℝ)^3951 := by
    have hnat : (229876167 : ℕ)^4975*50000000000000^3951 ≤ 24891741451863^3951*400000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229876167 400000000 24891741451863 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-735273851/5000000000 : ℝ), (4951517871/10000000000 : ℝ), (229876167/400000000 : ℝ)] ![(1789536670223/20000000000000 : ℝ), (41268833730413/100000000000000 : ℝ), (24891741451863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-735273851/5000000000 : ℝ)|^4975 ≤ (1789536670223/20000000000000 : ℝ)^3951
        have hw : |(-735273851/5000000000 : ℝ)|=(735273851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4951517871/10000000000 : ℝ)|^4975 ≤ (41268833730413/100000000000000 : ℝ)^3951
        have hw : |(4951517871/10000000000 : ℝ)|=(4951517871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229876167/400000000 : ℝ)|^4975 ≤ (24891741451863/50000000000000 : ℝ)^3951
        have hw : |(229876167/400000000 : ℝ)|=(229876167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_5 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203655999/10000000000 : ℝ)*x 0 + (-277684463/2500000000 : ℝ)*x 1 + (5746904843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203655999/10000000000 : ℝ)^4975 ≤ (8786438645339/20000000000000 : ℝ)^3951 := by
    have hnat : (5203655999 : ℕ)^4975*20000000000000^3951 ≤ 8786438645339^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203655999 10000000000 8786438645339 20000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277684463/2500000000 : ℝ)^4975 ≤ (6284316564859/100000000000000 : ℝ)^3951 := by
    have hnat : (277684463 : ℕ)^4975*100000000000000^3951 ≤ 6284316564859^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277684463 2500000000 6284316564859 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5746904843/10000000000 : ℝ)^4975 ≤ (2489174509507/5000000000000 : ℝ)^3951 := by
    have hnat : (5746904843 : ℕ)^4975*5000000000000^3951 ≤ 2489174509507^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5746904843 10000000000 2489174509507 5000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203655999/10000000000 : ℝ), (-277684463/2500000000 : ℝ), (5746904843/10000000000 : ℝ)] ![(8786438645339/20000000000000 : ℝ), (6284316564859/100000000000000 : ℝ), (2489174509507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203655999/10000000000 : ℝ)|^4975 ≤ (8786438645339/20000000000000 : ℝ)^3951
        have hw : |(5203655999/10000000000 : ℝ)|=(5203655999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277684463/2500000000 : ℝ)|^4975 ≤ (6284316564859/100000000000000 : ℝ)^3951
        have hw : |(-277684463/2500000000 : ℝ)|=(277684463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5746904843/10000000000 : ℝ)|^4975 ≤ (2489174509507/5000000000000 : ℝ)^3951
        have hw : |(5746904843/10000000000 : ℝ)|=(5746904843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_6 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2601827821/5000000000 : ℝ)*x 0 + (5746905541/10000000000 : ℝ)*x 1 + (-1110737317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601827821/5000000000 : ℝ)^4975 ≤ (10983047357887/25000000000000 : ℝ)^3951 := by
    have hnat : (2601827821 : ℕ)^4975*25000000000000^3951 ≤ 10983047357887^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601827821 5000000000 10983047357887 25000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5746905541/10000000000 : ℝ)^4975 ≤ (12445874450947/25000000000000 : ℝ)^3951 := by
    have hnat : (5746905541 : ℕ)^4975*25000000000000^3951 ≤ 12445874450947^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5746905541 10000000000 12445874450947 25000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110737317/10000000000 : ℝ)^4975 ≤ (6284312753443/100000000000000 : ℝ)^3951 := by
    have hnat : (1110737317 : ℕ)^4975*100000000000000^3951 ≤ 6284312753443^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110737317 10000000000 6284312753443 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601827821/5000000000 : ℝ), (5746905541/10000000000 : ℝ), (-1110737317/10000000000 : ℝ)] ![(10983047357887/25000000000000 : ℝ), (12445874450947/25000000000000 : ℝ), (6284312753443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601827821/5000000000 : ℝ)|^4975 ≤ (10983047357887/25000000000000 : ℝ)^3951
        have hw : |(2601827821/5000000000 : ℝ)|=(2601827821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5746905541/10000000000 : ℝ)|^4975 ≤ (12445874450947/25000000000000 : ℝ)^3951
        have hw : |(5746905541/10000000000 : ℝ)|=(5746905541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110737317/10000000000 : ℝ)|^4975 ≤ (6284312753443/100000000000000 : ℝ)^3951
        have hw : |(-1110737317/10000000000 : ℝ)|=(1110737317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s0_7 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1022438119/2500000000 : ℝ)*x 0 + (1309149917/2500000000 : ℝ)*x 1 + (25139173/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022438119/2500000000 : ℝ)^4975 ≤ (253424543187/781250000000 : ℝ)^3951 := by
    have hnat : (1022438119 : ℕ)^4975*781250000000^3951 ≤ 253424543187^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022438119 2500000000 253424543187 781250000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309149917/2500000000 : ℝ)^4975 ≤ (22141346572943/50000000000000 : ℝ)^3951 := by
    have hnat : (1309149917 : ℕ)^4975*50000000000000^3951 ≤ 22141346572943^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309149917 2500000000 22141346572943 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25139173/80000000 : ℝ)^4975 ≤ (11639482660251/50000000000000 : ℝ)^3951 := by
    have hnat : (25139173 : ℕ)^4975*50000000000000^3951 ≤ 11639482660251^3951*80000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25139173 80000000 11639482660251 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1022438119/2500000000 : ℝ), (1309149917/2500000000 : ℝ), (25139173/80000000 : ℝ)] ![(253424543187/781250000000 : ℝ), (22141346572943/50000000000000 : ℝ), (11639482660251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1022438119/2500000000 : ℝ)|^4975 ≤ (253424543187/781250000000 : ℝ)^3951
        have hw : |(1022438119/2500000000 : ℝ)|=(1022438119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309149917/2500000000 : ℝ)|^4975 ≤ (22141346572943/50000000000000 : ℝ)^3951
        have hw : |(1309149917/2500000000 : ℝ)|=(1309149917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25139173/80000000 : ℝ)|^4975 ≤ (11639482660251/50000000000000 : ℝ)^3951
        have hw : |(25139173/80000000 : ℝ)|=(25139173/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1664_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (511/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23063/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4971/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4971 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4971*1^1024 ≤ 0^1024*1^4971 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4971 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4971/1024 : ℝ) ≤ (1170047079192695447/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4971 ≤ (1170047079192695447/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4971*100000000000000000000^1024 ≤ 1170047079192695447^1024*5^4971 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1170047079192695447 100000000000000000000 4971 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1170047079192695447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4971 := by
      have hnat : (1 : ℕ)^1024*1^4971 ≤ 1^4971*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101170047079192695447/100000000000000000000 : ℝ) ≤ (10023991176588293/10000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (101170047079192695447/100000000000000000000 : ℝ)^1024 ≤ (10023991176588293/10000000000000000 : ℝ)^4971 := by
      have hnat : (101170047079192695447 : ℕ)^1024*10000000000000000^4971 ≤ 10023991176588293^4971*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101170047079192695447 100000000000000000000 10023991176588293 10000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023991176588293/10000000000000000 : ℝ)) (X := (101170047079192695447/100000000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51170047079192695447/50000000000000000000 : ℝ) ≤ (5023991176588293/5000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (51170047079192695447/50000000000000000000 : ℝ)^1024 ≤ (5023991176588293/5000000000000000 : ℝ)^4971 := by
      have hnat : (51170047079192695447 : ℕ)^1024*5000000000000000^4971 ≤ 5023991176588293^4971*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51170047079192695447 50000000000000000000 5023991176588293 5000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023991176588293/5000000000000000 : ℝ)) (X := (51170047079192695447/50000000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(23991176588293/4000000000000000 : ℝ)*(0 : ℝ))^(4971/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23991176588293/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1170047079192695447/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(23991176588293/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4971/1024 : ℝ) := by
    rw [show (1 : ℝ)+(23991176588293/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10023991176588293/10000000000000000 : ℝ) by norm_num, show 1+(1170047079192695447/100000000000000000000 : ℝ)+(0 : ℝ)=(101170047079192695447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1170047079192695447/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(23991176588293/4000000000000000 : ℝ)*(2/5 : ℝ))^(4971/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23991176588293/4000000000000000 : ℝ)*(2/5 : ℝ)=(5023991176588293/5000000000000000 : ℝ) by norm_num, show 1+2*(1170047079192695447/100000000000000000000 : ℝ)=(51170047079192695447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(23991176588293/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23991176588293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(23991176588293/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23991176588293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(23991176588293/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23991176588293/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-91775231/625000000 : ℝ)*X 0 0+(721027531/1250000000 : ℝ)*X 0 1+(493090587/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2716013013/5000000000 : ℝ)*X 1 0+(-1926735177/10000000000 : ℝ)*X 1 1+(2465453329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5432027753/10000000000 : ℝ)*X 2 0+(1232726383/2500000000 : ℝ)*X 2 1+(-1926734353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2042055399/5000000000 : ℝ)*X 0 0+(771568133/2500000000 : ℝ)*X 0 1+(5290869583/10000000000 : ℝ)*X 0 2+(2042055399/5000000000 : ℝ)*X 1 0+(771568133/2500000000 : ℝ)*X 1 1+(5290869583/10000000000 : ℝ)*X 1 2+(2042055399/5000000000 : ℝ)*X 2 0+(771568133/2500000000 : ℝ)*X 2 1+(5290869583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-735273851/5000000000 : ℝ)*X 0 0+(4951517871/10000000000 : ℝ)*X 0 1+(229876167/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5203655999/10000000000 : ℝ)*X 1 0+(-277684463/2500000000 : ℝ)*X 1 1+(5746904843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2601827821/5000000000 : ℝ)*X 2 0+(5746905541/10000000000 : ℝ)*X 2 1+(-1110737317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1022438119/2500000000 : ℝ)*X 0 0+(1309149917/2500000000 : ℝ)*X 0 1+(25139173/80000000 : ℝ)*X 0 2+(1022438119/2500000000 : ℝ)*X 1 0+(1309149917/2500000000 : ℝ)*X 1 1+(25139173/80000000 : ℝ)*X 1 2+(1022438119/2500000000 : ℝ)*X 2 0+(1309149917/2500000000 : ℝ)*X 2 1+(25139173/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55960150363089835172529/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55537411/50000000000000 : ℝ)*(base1) + (288471619/100000000000000 : ℝ)*(base19) + (564290377/100000000000000 : ℝ)*(base23) + (12985409/12500000000000 : ℝ)*(base24) + (18165591/50000000000000 : ℝ)*(upper5) + (205987150575351/25000000000000 : ℝ)*(major0) + (205987150575351/25000000000000 : ℝ)*(major1) + (205987150575351/25000000000000 : ℝ)*(major2) + (597147865197649/50000000000000 : ℝ)*(sp0) + (597148802495917/50000000000000 : ℝ)*(sp1) + (298574306322451/25000000000000 : ℝ)*(sp2) + (113399571545649/25000000000000 : ℝ)*(sp3) + (8883371/390625000000 : ℝ)*(sp4) + (839268401/100000000000000 : ℝ)*(sp7) + (226799618262909/50000000000000 : ℝ)*(f.failure) + (1194297893463453/100000000000000 : ℝ)*(f.sum) + (106179795234157/50000000000000000000000000000 : ℝ)*base66 + (40730006965843/100000000000000000000000000000 : ℝ)*base67 + (67691385665843/100000000000000000000000000000 : ℝ)*base69 + (11170784165843/100000000000000000000000000000 : ℝ)*base71 + (146383765134157/50000000000000000000000000000 : ℝ)*base74 + (197939285534157/100000000000000000000000000000 : ℝ)*base76 + (112124911365843/100000000000000000000000000000 : ℝ)*base77 + (59877765834157/100000000000000000000000000000 : ℝ)*base80 + (23348163084157/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1411893/5000000000000000000000 : ℝ)*base90 + (1411893/5000000000000000000000 : ℝ)*base92 + (1411893/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (824360211569492788408071/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293445009/100000000000000 : ℝ)*(base23) + (143050573/50000000000000 : ℝ)*(base39) + (21368199/50000000000000 : ℝ)*(upper2) + (9170723/25000000000000 : ℝ)*(upper3) + (1429871/800000000000 : ℝ)*(upper5) + (867378338716699/100000000000000 : ℝ)*(major0) + (867378338716699/100000000000000 : ℝ)*(major1) + (867378052615553/100000000000000 : ℝ)*(major2) + (144918467/25000000000000 : ℝ)*(sp1) + (916173281/100000000000000 : ℝ)*(sp2) + (3143120322227/250000000000 : ℝ)*(sp4) + (314311887304233/25000000000000 : ℝ)*(sp5) + (1257247205373657/100000000000000 : ℝ)*(sp6) + (477508125048077/100000000000000 : ℝ)*(sp7) + (477508125048077/100000000000000 : ℝ)*(f.failure) + (1257248414991947/100000000000000 : ℝ)*(f.sum) + (15398888931459/100000000000000000000000000000 : ℝ)*base65 + (1385177595121029/400000000000000000000000000000 : ℝ)*base67 + (3838214637004807/400000000000000000000000000000 : ℝ)*base69 + (191753225678971/400000000000000000000000000000 : ℝ)*base72 + (442756220531459/100000000000000000000000000000 : ℝ)*base73 + (1470564709004807/400000000000000000000000000000 : ℝ)*base75 + (433164928595193/400000000000000000000000000000 : ℝ)*base78 + (2032918258995193/400000000000000000000000000000 : ℝ)*base80 + (1031774754404807/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (9309371/10000000000000000000000 : ℝ)*base89 + (9309371/10000000000000000000000 : ℝ)*base91 + (9309371/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1664_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (511/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1664_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1664_s1_0 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156862727/1000000000 : ℝ)*x 0 + (2743075229/5000000000 : ℝ)*x 1 + (5147715193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156862727/1000000000 : ℝ)^4975 ≤ (970551714961/10000000000000 : ℝ)^3951 := by
    have hnat : (156862727 : ℕ)^4975*10000000000000^3951 ≤ 970551714961^3951*1000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156862727 1000000000 970551714961 10000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743075229/5000000000 : ℝ)^4975 ≤ (5869518351449/12500000000000 : ℝ)^3951 := by
    have hnat : (2743075229 : ℕ)^4975*12500000000000^3951 ≤ 5869518351449^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743075229 5000000000 5869518351449 12500000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147715193/10000000000 : ℝ)^4975 ≤ (43338336026071/100000000000000 : ℝ)^3951 := by
    have hnat : (5147715193 : ℕ)^4975*100000000000000^3951 ≤ 43338336026071^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147715193 10000000000 43338336026071 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156862727/1000000000 : ℝ), (2743075229/5000000000 : ℝ), (5147715193/10000000000 : ℝ)] ![(970551714961/10000000000000 : ℝ), (5869518351449/12500000000000 : ℝ), (43338336026071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156862727/1000000000 : ℝ)|^4975 ≤ (970551714961/10000000000000 : ℝ)^3951
        have hw : |(-156862727/1000000000 : ℝ)|=(156862727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743075229/5000000000 : ℝ)|^4975 ≤ (5869518351449/12500000000000 : ℝ)^3951
        have hw : |(2743075229/5000000000 : ℝ)|=(2743075229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147715193/10000000000 : ℝ)|^4975 ≤ (43338336026071/100000000000000 : ℝ)^3951
        have hw : |(5147715193/10000000000 : ℝ)|=(5147715193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_1 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678496423/5000000000 : ℝ)*x 0 + (-872132839/5000000000 : ℝ)*x 1 + (40216523/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678496423/5000000000 : ℝ)^4975 ≤ (45568445438523/100000000000000 : ℝ)^3951 := by
    have hnat : (2678496423 : ℕ)^4975*100000000000000^3951 ≤ 45568445438523^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678496423 5000000000 45568445438523 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872132839/5000000000 : ℝ)^4975 ≤ (2773305291097/25000000000000 : ℝ)^3951 := by
    have hnat : (872132839 : ℕ)^4975*25000000000000^3951 ≤ 2773305291097^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872132839 5000000000 2773305291097 25000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40216523/78125000 : ℝ)^4975 ≤ (1083458334661/2500000000000 : ℝ)^3951 := by
    have hnat : (40216523 : ℕ)^4975*2500000000000^3951 ≤ 1083458334661^3951*78125000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40216523 78125000 1083458334661 2500000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678496423/5000000000 : ℝ), (-872132839/5000000000 : ℝ), (40216523/78125000 : ℝ)] ![(45568445438523/100000000000000 : ℝ), (2773305291097/25000000000000 : ℝ), (1083458334661/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678496423/5000000000 : ℝ)|^4975 ≤ (45568445438523/100000000000000 : ℝ)^3951
        have hw : |(2678496423/5000000000 : ℝ)|=(2678496423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-872132839/5000000000 : ℝ)|^4975 ≤ (2773305291097/25000000000000 : ℝ)^3951
        have hw : |(-872132839/5000000000 : ℝ)|=(872132839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40216523/78125000 : ℝ)|^4975 ≤ (1083458334661/2500000000000 : ℝ)^3951
        have hw : |(40216523/78125000 : ℝ)|=(40216523/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_2 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678496147/5000000000 : ℝ)*x 0 + (2573857769/5000000000 : ℝ)*x 1 + (-174426563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678496147/5000000000 : ℝ)^4975 ≤ (22784219763031/50000000000000 : ℝ)^3951 := by
    have hnat : (2678496147 : ℕ)^4975*50000000000000^3951 ≤ 22784219763031^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678496147 5000000000 22784219763031 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573857769/5000000000 : ℝ)^4975 ≤ (4333833968339/10000000000000 : ℝ)^3951 := by
    have hnat : (2573857769 : ℕ)^4975*10000000000000^3951 ≤ 4333833968339^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573857769 5000000000 4333833968339 10000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174426563/1000000000 : ℝ)^4975 ≤ (5546610389999/50000000000000 : ℝ)^3951 := by
    have hnat : (174426563 : ℕ)^4975*50000000000000^3951 ≤ 5546610389999^3951*1000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174426563 1000000000 5546610389999 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678496147/5000000000 : ℝ), (2573857769/5000000000 : ℝ), (-174426563/1000000000 : ℝ)] ![(22784219763031/50000000000000 : ℝ), (4333833968339/10000000000000 : ℝ), (5546610389999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678496147/5000000000 : ℝ)|^4975 ≤ (22784219763031/50000000000000 : ℝ)^3951
        have hw : |(2678496147/5000000000 : ℝ)|=(2678496147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573857769/5000000000 : ℝ)|^4975 ≤ (4333833968339/10000000000000 : ℝ)^3951
        have hw : |(2573857769/5000000000 : ℝ)|=(2573857769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174426563/1000000000 : ℝ)|^4975 ≤ (5546610389999/50000000000000 : ℝ)^3951
        have hw : |(-174426563/1000000000 : ℝ)|=(174426563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_3 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163732773/10000000000 : ℝ)*x 0 + (747019993/2000000000 : ℝ)*x 1 + (4626179/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163732773/10000000000 : ℝ)^4975 ≤ (2073683034059/6250000000000 : ℝ)^3951 := by
    have hnat : (4163732773 : ℕ)^4975*6250000000000^3951 ≤ 2073683034059^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163732773 10000000000 2073683034059 6250000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747019993/2000000000 : ℝ)^4975 ≤ (28937013439477/100000000000000 : ℝ)^3951 := by
    have hnat : (747019993 : ℕ)^4975*100000000000000^3951 ≤ 28937013439477^3951*2000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747019993 2000000000 28937013439477 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4626179/10000000 : ℝ)^4975 ≤ (18942029002219/50000000000000 : ℝ)^3951 := by
    have hnat : (4626179 : ℕ)^4975*50000000000000^3951 ≤ 18942029002219^3951*10000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4626179 10000000 18942029002219 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163732773/10000000000 : ℝ), (747019993/2000000000 : ℝ), (4626179/10000000 : ℝ)] ![(2073683034059/6250000000000 : ℝ), (28937013439477/100000000000000 : ℝ), (18942029002219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163732773/10000000000 : ℝ)|^4975 ≤ (2073683034059/6250000000000 : ℝ)^3951
        have hw : |(4163732773/10000000000 : ℝ)|=(4163732773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747019993/2000000000 : ℝ)|^4975 ≤ (28937013439477/100000000000000 : ℝ)^3951
        have hw : |(747019993/2000000000 : ℝ)|=(747019993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4626179/10000000 : ℝ)|^4975 ≤ (18942029002219/50000000000000 : ℝ)^3951
        have hw : |(4626179/10000000 : ℝ)|=(4626179/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_4 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1568766231/10000000000 : ℝ)*x 0 + (2575538517/5000000000 : ℝ)*x 1 + (685342829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1568766231/10000000000 : ℝ)^4975 ≤ (9706599786677/100000000000000 : ℝ)^3951 := by
    have hnat : (1568766231 : ℕ)^4975*100000000000000^3951 ≤ 9706599786677^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568766231 10000000000 9706599786677 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575538517/5000000000 : ℝ)^4975 ≤ (2710873604203/6250000000000 : ℝ)^3951 := by
    have hnat : (2575538517 : ℕ)^4975*6250000000000^3951 ≤ 2710873604203^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575538517 5000000000 2710873604203 6250000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685342829/1250000000 : ℝ)^4975 ≤ (23459711267923/50000000000000 : ℝ)^3951 := by
    have hnat : (685342829 : ℕ)^4975*50000000000000^3951 ≤ 23459711267923^3951*1250000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685342829 1250000000 23459711267923 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1568766231/10000000000 : ℝ), (2575538517/5000000000 : ℝ), (685342829/1250000000 : ℝ)] ![(9706599786677/100000000000000 : ℝ), (2710873604203/6250000000000 : ℝ), (23459711267923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1568766231/10000000000 : ℝ)|^4975 ≤ (9706599786677/100000000000000 : ℝ)^3951
        have hw : |(-1568766231/10000000000 : ℝ)|=(1568766231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575538517/5000000000 : ℝ)|^4975 ≤ (2710873604203/6250000000000 : ℝ)^3951
        have hw : |(2575538517/5000000000 : ℝ)|=(2575538517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685342829/1250000000 : ℝ)|^4975 ≤ (23459711267923/50000000000000 : ℝ)^3951
        have hw : |(685342829/1250000000 : ℝ)|=(685342829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_5 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316595579/2500000000 : ℝ)*x 0 + (-1409238541/10000000000 : ℝ)*x 1 + (548274261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316595579/2500000000 : ℝ)^4975 ≤ (5575006766019/12500000000000 : ℝ)^3951 := by
    have hnat : (1316595579 : ℕ)^4975*12500000000000^3951 ≤ 5575006766019^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316595579 2500000000 5575006766019 12500000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1409238541/10000000000 : ℝ)^4975 ≤ (8480523551437/100000000000000 : ℝ)^3951 := by
    have hnat : (1409238541 : ℕ)^4975*100000000000000^3951 ≤ 8480523551437^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409238541 10000000000 8480523551437 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548274261/1000000000 : ℝ)^4975 ≤ (46919422298783/100000000000000 : ℝ)^3951 := by
    have hnat : (548274261 : ℕ)^4975*100000000000000^3951 ≤ 46919422298783^3951*1000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548274261 1000000000 46919422298783 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316595579/2500000000 : ℝ), (-1409238541/10000000000 : ℝ), (548274261/1000000000 : ℝ)] ![(5575006766019/12500000000000 : ℝ), (8480523551437/100000000000000 : ℝ), (46919422298783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316595579/2500000000 : ℝ)|^4975 ≤ (5575006766019/12500000000000 : ℝ)^3951
        have hw : |(1316595579/2500000000 : ℝ)|=(1316595579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1409238541/10000000000 : ℝ)|^4975 ≤ (8480523551437/100000000000000 : ℝ)^3951
        have hw : |(-1409238541/10000000000 : ℝ)|=(1409238541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548274261/1000000000 : ℝ)|^4975 ≤ (46919422298783/100000000000000 : ℝ)^3951
        have hw : |(548274261/1000000000 : ℝ)|=(548274261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_6 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053276463/2000000000 : ℝ)*x 0 + (548274261/1000000000 : ℝ)*x 1 + (-88077409/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053276463/2000000000 : ℝ)^4975 ≤ (2787503382343/6250000000000 : ℝ)^3951 := by
    have hnat : (1053276463 : ℕ)^4975*6250000000000^3951 ≤ 2787503382343^3951*2000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053276463 2000000000 2787503382343 6250000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548274261/1000000000 : ℝ)^4975 ≤ (46919422298783/100000000000000 : ℝ)^3951 := by
    have hnat : (548274261 : ℕ)^4975*100000000000000^3951 ≤ 46919422298783^3951*1000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548274261 1000000000 46919422298783 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88077409/625000000 : ℝ)^4975 ≤ (848052357417/10000000000000 : ℝ)^3951 := by
    have hnat : (88077409 : ℕ)^4975*10000000000000^3951 ≤ 848052357417^3951*625000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88077409 625000000 848052357417 10000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053276463/2000000000 : ℝ), (548274261/1000000000 : ℝ), (-88077409/625000000 : ℝ)] ![(2787503382343/6250000000000 : ℝ), (46919422298783/100000000000000 : ℝ), (848052357417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053276463/2000000000 : ℝ)|^4975 ≤ (2787503382343/6250000000000 : ℝ)^3951
        have hw : |(1053276463/2000000000 : ℝ)|=(1053276463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548274261/1000000000 : ℝ)|^4975 ≤ (46919422298783/100000000000000 : ℝ)^3951
        have hw : |(548274261/1000000000 : ℝ)|=(548274261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88077409/625000000 : ℝ)|^4975 ≤ (848052357417/10000000000000 : ℝ)^3951
        have hw : |(-88077409/625000000 : ℝ)|=(88077409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s1_7 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164099639/10000000000 : ℝ)*x 0 + (288582987/625000000 : ℝ)*x 1 + (748814679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164099639/10000000000 : ℝ)^4975 ≤ (33182609648091/100000000000000 : ℝ)^3951 := by
    have hnat : (4164099639 : ℕ)^4975*100000000000000^3951 ≤ 33182609648091^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164099639 10000000000 33182609648091 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288582987/625000000 : ℝ)^4975 ≤ (37792811776573/100000000000000 : ℝ)^3951 := by
    have hnat : (288582987 : ℕ)^4975*100000000000000^3951 ≤ 37792811776573^3951*625000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288582987 625000000 37792811776573 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748814679/2000000000 : ℝ)^4975 ≤ (29024578553651/100000000000000 : ℝ)^3951 := by
    have hnat : (748814679 : ℕ)^4975*100000000000000^3951 ≤ 29024578553651^3951*2000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748814679 2000000000 29024578553651 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164099639/10000000000 : ℝ), (288582987/625000000 : ℝ), (748814679/2000000000 : ℝ)] ![(33182609648091/100000000000000 : ℝ), (37792811776573/100000000000000 : ℝ), (29024578553651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164099639/10000000000 : ℝ)|^4975 ≤ (33182609648091/100000000000000 : ℝ)^3951
        have hw : |(4164099639/10000000000 : ℝ)|=(4164099639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(288582987/625000000 : ℝ)|^4975 ≤ (37792811776573/100000000000000 : ℝ)^3951
        have hw : |(288582987/625000000 : ℝ)|=(288582987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748814679/2000000000 : ℝ)|^4975 ≤ (29024578553651/100000000000000 : ℝ)^3951
        have hw : |(748814679/2000000000 : ℝ)|=(748814679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1664_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (511/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9939/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1071/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (511/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (511/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (511/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (511/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (511/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (511/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (511/10000 : ℝ) ^ (4971/1024 : ℝ) ≤ (26854022873553/50000000000000000000 : ℝ) := by
    have hpowers : (511/10000 : ℝ)^4971 ≤ (26854022873553/50000000000000000000 : ℝ)^1024 := by
      have hnat : (511 : ℕ)^4971*50000000000000000000^1024 ≤ 26854022873553^1024*10000^4971 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        511 10000 26854022873553 50000000000000000000 4971 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (511/10000 : ℝ)) (X := (26854022873553/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23063/100000 : ℝ) ^ (4971/1024 : ℝ) ≤ (10096939092208647/12500000000000000000 : ℝ) := by
    have hpowers : (23063/100000 : ℝ)^4971 ≤ (10096939092208647/12500000000000000000 : ℝ)^1024 := by
      have hnat : (23063 : ℕ)^4971*12500000000000000000^1024 ≤ 10096939092208647^1024*100000^4971 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23063 100000 10096939092208647 12500000000000000000 4971 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23063/100000 : ℝ)) (X := (10096939092208647/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000026854022873553/25000000000000000000 : ℝ) ≤ (10000002212714359/10000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (25000026854022873553/25000000000000000000 : ℝ)^1024 ≤ (10000002212714359/10000000000000000 : ℝ)^4971 := by
      have hnat : (25000026854022873553 : ℕ)^1024*10000000000000000^4971 ≤ 10000002212714359^4971*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000026854022873553 25000000000000000000 10000002212714359 10000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002212714359/10000000000000000 : ℝ)) (X := (25000026854022873553/25000000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50040414610391708141/50000000000000000000 : ℝ) ≤ (5000832252814207/5000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (50040414610391708141/50000000000000000000 : ℝ)^1024 ≤ (5000832252814207/5000000000000000 : ℝ)^4971 := by
      have hnat : (50040414610391708141 : ℕ)^1024*5000000000000000^4971 ≤ 5000832252814207^4971*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040414610391708141 50000000000000000000 5000832252814207 5000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000832252814207/5000000000000000 : ℝ)) (X := (50040414610391708141/50000000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6260096939092208647/6250000000000000000 : ℝ) ≤ (10003326798542469/10000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (6260096939092208647/6250000000000000000 : ℝ)^1024 ≤ (10003326798542469/10000000000000000 : ℝ)^4971 := by
      have hnat : (6260096939092208647 : ℕ)^1024*10000000000000000^4971 ≤ 10003326798542469^4971*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260096939092208647 6250000000000000000 10003326798542469 10000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003326798542469/10000000000000000 : ℝ)) (X := (6260096939092208647/6250000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26854022873553/50000000000000000000 : ℝ) ≤ ((179513051091279245027/179530000000000000000 : ℝ)+2*(332458582811/359060000000000 : ℝ)*(511/10000 : ℝ))^(4971/1024 : ℝ) := by
    rw [show (179513051091279245027/179530000000000000000 : ℝ)+2*(332458582811/359060000000000 : ℝ)*(511/10000 : ℝ)=(10000002212714359/10000000000000000 : ℝ) by norm_num, show 1+2*(26854022873553/50000000000000000000 : ℝ)=(25000026854022873553/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10096939092208647/12500000000000000000 : ℝ)+(26854022873553/50000000000000000000 : ℝ) ≤ ((179513051091279245027/179530000000000000000 : ℝ)+(332458582811/359060000000000 : ℝ)*((23063/100000 : ℝ)+(511/10000 : ℝ)))^(4971/1024 : ℝ) := by
    rw [show (179513051091279245027/179530000000000000000 : ℝ)+(332458582811/359060000000000 : ℝ)*((23063/100000 : ℝ)+(511/10000 : ℝ))=(5000832252814207/5000000000000000 : ℝ) by norm_num, show 1+(10096939092208647/12500000000000000000 : ℝ)+(26854022873553/50000000000000000000 : ℝ)=(50040414610391708141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10096939092208647/12500000000000000000 : ℝ) ≤ ((179513051091279245027/179530000000000000000 : ℝ)+2*(332458582811/359060000000000 : ℝ)*(23063/100000 : ℝ))^(4971/1024 : ℝ) := by
    rw [show (179513051091279245027/179530000000000000000 : ℝ)+2*(332458582811/359060000000000 : ℝ)*(23063/100000 : ℝ)=(10003326798542469/10000000000000000 : ℝ) by norm_num, show 1+2*(10096939092208647/12500000000000000000 : ℝ)=(6260096939092208647/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (179513051091279245027/179530000000000000000 : ℝ)*(X 1 0+X 2 0)+(332458582811/359060000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (511/10000 : ℝ)) (hi := (23063/100000 : ℝ)) (c := (179513051091279245027/179530000000000000000 : ℝ)) (alpha := (332458582811/359060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (179513051091279245027/179530000000000000000 : ℝ)*(X 0 1+X 2 1)+(332458582811/359060000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (511/10000 : ℝ)) (hi := (23063/100000 : ℝ)) (c := (179513051091279245027/179530000000000000000 : ℝ)) (alpha := (332458582811/359060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (179513051091279245027/179530000000000000000 : ℝ)*(X 0 2+X 1 2)+(332458582811/359060000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (511/10000 : ℝ)) (hi := (23063/100000 : ℝ)) (c := (179513051091279245027/179530000000000000000 : ℝ)) (alpha := (332458582811/359060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156862727/1000000000 : ℝ)*X 0 0+(2743075229/5000000000 : ℝ)*X 0 1+(5147715193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678496423/5000000000 : ℝ)*X 1 0+(-872132839/5000000000 : ℝ)*X 1 1+(40216523/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678496147/5000000000 : ℝ)*X 2 0+(2573857769/5000000000 : ℝ)*X 2 1+(-174426563/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4163732773/10000000000 : ℝ)*X 0 0+(747019993/2000000000 : ℝ)*X 0 1+(4626179/10000000 : ℝ)*X 0 2+(4163732773/10000000000 : ℝ)*X 1 0+(747019993/2000000000 : ℝ)*X 1 1+(4626179/10000000 : ℝ)*X 1 2+(4163732773/10000000000 : ℝ)*X 2 0+(747019993/2000000000 : ℝ)*X 2 1+(4626179/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1568766231/10000000000 : ℝ)*X 0 0+(2575538517/5000000000 : ℝ)*X 0 1+(685342829/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316595579/2500000000 : ℝ)*X 1 0+(-1409238541/10000000000 : ℝ)*X 1 1+(548274261/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053276463/2000000000 : ℝ)*X 2 0+(548274261/1000000000 : ℝ)*X 2 1+(-88077409/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164099639/10000000000 : ℝ)*X 0 0+(288582987/625000000 : ℝ)*X 0 1+(748814679/2000000000 : ℝ)*X 0 2+(4164099639/10000000000 : ℝ)*X 1 0+(288582987/625000000 : ℝ)*X 1 1+(748814679/2000000000 : ℝ)*X 1 2+(4164099639/10000000000 : ℝ)*X 2 0+(288582987/625000000 : ℝ)*X 2 1+(748814679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8248497533815886941808429049/8976500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1104226909/100000000000000 : ℝ)*(base19) + (74503839/12500000000000 : ℝ)*(base23) + (20024911/10000000000000 : ℝ)*(upper3) + (1705247/1562500000000 : ℝ)*(upper4) + (8760183/20000000000000 : ℝ)*(upper5) + (407703523034427/20000000000000 : ℝ)*(major0) + (407703523034427/20000000000000 : ℝ)*(major1) + (254814701896517/12500000000000 : ℝ)*(major2) + (1477392504023773/50000000000000 : ℝ)*(sp0) + (1477395861723243/50000000000000 : ℝ)*(sp1) + (1477396115821341/50000000000000 : ℝ)*(sp2) + (561119069131157/50000000000000 : ℝ)*(sp3) + (7819625849/100000000000000 : ℝ)*(sp4) + (2116889293/50000000000000 : ℝ)*(sp7) + (11222423720409/1000000000000 : ℝ)*(f.failure) + (1477396413836697/50000000000000 : ℝ)*(f.sum) + (8216228144743/2762000000000000000000000000 : ℝ)*base65 + (4348331579645544529/3590600000000000000000000000000000 : ℝ)*base67 + (10982638806752683459/2244125000000000000000000000000000 : ℝ)*base69 + (10283999947560055471/3590600000000000000000000000000000 : ℝ)*base72 + (12271090026269/2762000000000000000000000000 : ℝ)*base73 + (27242612923050933459/2244125000000000000000000000000000 : ℝ)*base75 + (9540016868467644529/3590600000000000000000000000000000 : ℝ)*base77 + (18802923396995244529/3590600000000000000000000000000000 : ℝ)*base79 + (12564815167089/3590600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (110607/100000000000000000000 : ℝ)*base89 + (110607/100000000000000000000 : ℝ)*base91 + (889393/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45495561543922714697689685889/8976500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164769159/20000000000000 : ℝ)*(base19) + (875208221/100000000000000 : ℝ)*(base23) + (116414707/100000000000000 : ℝ)*(upper3) + (472367/2000000000000 : ℝ)*(lower4) + (23471103/20000000000000 : ℝ)*(upper5) + (2080113290561369/100000000000000 : ℝ)*(major0) + (2080113290561369/100000000000000 : ℝ)*(major1) + (2080113290561369/100000000000000 : ℝ)*(major2) + (232354371/3125000000000 : ℝ)*(sp1) + (980915463/12500000000000 : ℝ)*(sp2) + (3015084836782209/100000000000000 : ℝ)*(sp4) + (1507538288798271/50000000000000 : ℝ)*(sp5) + (603015222850057/20000000000000 : ℝ)*(sp6) + (1145141575397313/100000000000000 : ℝ)*(sp7) + (1145141575397313/100000000000000 : ℝ)*(f.failure) + (3015084836782209/100000000000000 : ℝ)*(f.sum) + (646261318139/718120000000000000000000000 : ℝ)*base65 + (111565476142555061963/17953000000000000000000000000000000 : ℝ)*base67 + (30703176368442061963/17953000000000000000000000000000000 : ℝ)*base69 + (95905962457961938037/17953000000000000000000000000000000 : ℝ)*base72 + (26700549930757/3590600000000000000000000000 : ℝ)*base73 + (77770065049657938037/17953000000000000000000000000000000 : ℝ)*base76 + (74454636694912938037/17953000000000000000000000000000000 : ℝ)*base78 + (127765401266132938037/17953000000000000000000000000000000 : ℝ)*base80 + (5119647637799/1122062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (30813401/10000000000000000000000 : ℝ)*base90 + (30813401/10000000000000000000000 : ℝ)*base92 + (30813401/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1664_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (511/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9939/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1071/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1664_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1664_s2_0 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1576685311/10000000000 : ℝ)*x 0 + (5446224437/10000000000 : ℝ)*x 1 + (5182311169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1576685311/10000000000 : ℝ)^4975 ≤ (9768337896101/100000000000000 : ℝ)^3951 := by
    have hnat : (1576685311 : ℕ)^4975*100000000000000^3951 ≤ 9768337896101^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576685311 10000000000 9768337896101 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446224437/10000000000 : ℝ)^4975 ≤ (23263128914613/50000000000000 : ℝ)^3951 := by
    have hnat : (5446224437 : ℕ)^4975*50000000000000^3951 ≤ 23263128914613^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446224437 10000000000 23263128914613 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182311169/10000000000 : ℝ)^4975 ≤ (2185270213177/5000000000000 : ℝ)^3951 := by
    have hnat : (5182311169 : ℕ)^4975*5000000000000^3951 ≤ 2185270213177^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182311169 10000000000 2185270213177 5000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1576685311/10000000000 : ℝ), (5446224437/10000000000 : ℝ), (5182311169/10000000000 : ℝ)] ![(9768337896101/100000000000000 : ℝ), (23263128914613/50000000000000 : ℝ), (2185270213177/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1576685311/10000000000 : ℝ)|^4975 ≤ (9768337896101/100000000000000 : ℝ)^3951
        have hw : |(-1576685311/10000000000 : ℝ)|=(1576685311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446224437/10000000000 : ℝ)|^4975 ≤ (23263128914613/50000000000000 : ℝ)^3951
        have hw : |(5446224437/10000000000 : ℝ)|=(5446224437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182311169/10000000000 : ℝ)|^4975 ≤ (2185270213177/5000000000000 : ℝ)^3951
        have hw : |(5182311169/10000000000 : ℝ)|=(5182311169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_1 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336594277/2500000000 : ℝ)*x 0 + (-1712548137/10000000000 : ℝ)*x 1 + (5182311339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336594277/2500000000 : ℝ)^4975 ≤ (45454769696339/100000000000000 : ℝ)^3951 := by
    have hnat : (1336594277 : ℕ)^4975*100000000000000^3951 ≤ 45454769696339^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336594277 2500000000 45454769696339 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1712548137/10000000000 : ℝ)^4975 ≤ (2167964843531/20000000000000 : ℝ)^3951 := by
    have hnat : (1712548137 : ℕ)^4975*20000000000000^3951 ≤ 2167964843531^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712548137 10000000000 2167964843531 20000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182311339/10000000000 : ℝ)^4975 ≤ (10926351517207/25000000000000 : ℝ)^3951 := by
    have hnat : (5182311339 : ℕ)^4975*25000000000000^3951 ≤ 10926351517207^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182311339 10000000000 10926351517207 25000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336594277/2500000000 : ℝ), (-1712548137/10000000000 : ℝ), (5182311339/10000000000 : ℝ)] ![(45454769696339/100000000000000 : ℝ), (2167964843531/20000000000000 : ℝ), (10926351517207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336594277/2500000000 : ℝ)|^4975 ≤ (45454769696339/100000000000000 : ℝ)^3951
        have hw : |(1336594277/2500000000 : ℝ)|=(1336594277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1712548137/10000000000 : ℝ)|^4975 ≤ (2167964843531/20000000000000 : ℝ)^3951
        have hw : |(-1712548137/10000000000 : ℝ)|=(1712548137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182311339/10000000000 : ℝ)|^4975 ≤ (10926351517207/25000000000000 : ℝ)^3951
        have hw : |(5182311339/10000000000 : ℝ)|=(5182311339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_2 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346377181/10000000000 : ℝ)*x 0 + (323894449/625000000 : ℝ)*x 1 + (-856274123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346377181/10000000000 : ℝ)^4975 ≤ (45454770477839/100000000000000 : ℝ)^3951 := by
    have hnat : (5346377181 : ℕ)^4975*100000000000000^3951 ≤ 45454770477839^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346377181 10000000000 45454770477839 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323894449/625000000 : ℝ)^4975 ≤ (4370540442283/10000000000000 : ℝ)^3951 := by
    have hnat : (323894449 : ℕ)^4975*10000000000000^3951 ≤ 4370540442283^3951*625000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323894449 625000000 4370540442283 10000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (856274123/5000000000 : ℝ)^4975 ≤ (6774890679/62500000000 : ℝ)^3951 := by
    have hnat : (856274123 : ℕ)^4975*62500000000^3951 ≤ 6774890679^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856274123 5000000000 6774890679 62500000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346377181/10000000000 : ℝ), (323894449/625000000 : ℝ), (-856274123/5000000000 : ℝ)] ![(45454770477839/100000000000000 : ℝ), (4370540442283/10000000000000 : ℝ), (6774890679/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346377181/10000000000 : ℝ)|^4975 ≤ (45454770477839/100000000000000 : ℝ)^3951
        have hw : |(5346377181/10000000000 : ℝ)|=(5346377181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323894449/625000000 : ℝ)|^4975 ≤ (4370540442283/10000000000000 : ℝ)^3951
        have hw : |(323894449/625000000 : ℝ)|=(323894449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-856274123/5000000000 : ℝ)|^4975 ≤ (6774890679/62500000000 : ℝ)^3951
        have hw : |(-856274123/5000000000 : ℝ)|=(856274123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_3 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084879723/5000000000 : ℝ)*x 0 + (3832611227/10000000000 : ℝ)*x 1 + (181099113/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084879723/5000000000 : ℝ)^4975 ≤ (6647882066387/20000000000000 : ℝ)^3951 := by
    have hnat : (2084879723 : ℕ)^4975*20000000000000^3951 ≤ 6647882066387^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084879723 5000000000 6647882066387 20000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3832611227/10000000000 : ℝ)^4975 ≤ (29891455915011/100000000000000 : ℝ)^3951 := by
    have hnat : (3832611227 : ℕ)^4975*100000000000000^3951 ≤ 29891455915011^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3832611227 10000000000 29891455915011 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181099113/400000000 : ℝ)^4975 ≤ (18434566868307/50000000000000 : ℝ)^3951 := by
    have hnat : (181099113 : ℕ)^4975*50000000000000^3951 ≤ 18434566868307^3951*400000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181099113 400000000 18434566868307 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084879723/5000000000 : ℝ), (3832611227/10000000000 : ℝ), (181099113/400000000 : ℝ)] ![(6647882066387/20000000000000 : ℝ), (29891455915011/100000000000000 : ℝ), (18434566868307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084879723/5000000000 : ℝ)|^4975 ≤ (6647882066387/20000000000000 : ℝ)^3951
        have hw : |(2084879723/5000000000 : ℝ)|=(2084879723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3832611227/10000000000 : ℝ)|^4975 ≤ (29891455915011/100000000000000 : ℝ)^3951
        have hw : |(3832611227/10000000000 : ℝ)|=(3832611227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181099113/400000000 : ℝ)|^4975 ≤ (18434566868307/50000000000000 : ℝ)^3951
        have hw : |(181099113/400000000 : ℝ)|=(181099113/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_4 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1576751633/10000000000 : ℝ)*x 0 + (259218031/500000000 : ℝ)*x 1 + (85064889/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1576751633/10000000000 : ℝ)^4975 ≤ (488442764523/5000000000000 : ℝ)^3951 := by
    have hnat : (1576751633 : ℕ)^4975*5000000000000^3951 ≤ 488442764523^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576751633 10000000000 488442764523 5000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259218031/500000000 : ℝ)^4975 ≤ (43727169205029/100000000000000 : ℝ)^3951 := by
    have hnat : (259218031 : ℕ)^4975*100000000000000^3951 ≤ 43727169205029^3951*500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259218031 500000000 43727169205029 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85064889/156250000 : ℝ)^4975 ≤ (46503975490689/100000000000000 : ℝ)^3951 := by
    have hnat : (85064889 : ℕ)^4975*100000000000000^3951 ≤ 46503975490689^3951*156250000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85064889 156250000 46503975490689 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1576751633/10000000000 : ℝ), (259218031/500000000 : ℝ), (85064889/156250000 : ℝ)] ![(488442764523/5000000000000 : ℝ), (43727169205029/100000000000000 : ℝ), (46503975490689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1576751633/10000000000 : ℝ)|^4975 ≤ (488442764523/5000000000000 : ℝ)^3951
        have hw : |(-1576751633/10000000000 : ℝ)|=(1576751633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259218031/500000000 : ℝ)|^4975 ≤ (43727169205029/100000000000000 : ℝ)^3951
        have hw : |(259218031/500000000 : ℝ)|=(259218031/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85064889/156250000 : ℝ)|^4975 ≤ (46503975490689/100000000000000 : ℝ)^3951
        have hw : |(85064889/156250000 : ℝ)|=(85064889/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_5 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637880503/5000000000 : ℝ)*x 0 + (-362676619/2500000000 : ℝ)*x 1 + (5444152927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637880503/5000000000 : ℝ)^4975 ≤ (44700088997239/100000000000000 : ℝ)^3951 := by
    have hnat : (2637880503 : ℕ)^4975*100000000000000^3951 ≤ 44700088997239^3951*5000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637880503 5000000000 44700088997239 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362676619/2500000000 : ℝ)^4975 ≤ (2198983792491/25000000000000 : ℝ)^3951 := by
    have hnat : (362676619 : ℕ)^4975*25000000000000^3951 ≤ 2198983792491^3951*2500000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362676619 2500000000 2198983792491 25000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444152927/10000000000 : ℝ)^4975 ≤ (46503975824121/100000000000000 : ℝ)^3951 := by
    have hnat : (5444152927 : ℕ)^4975*100000000000000^3951 ≤ 46503975824121^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444152927 10000000000 46503975824121 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637880503/5000000000 : ℝ), (-362676619/2500000000 : ℝ), (5444152927/10000000000 : ℝ)] ![(44700088997239/100000000000000 : ℝ), (2198983792491/25000000000000 : ℝ), (46503975824121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637880503/5000000000 : ℝ)|^4975 ≤ (44700088997239/100000000000000 : ℝ)^3951
        have hw : |(2637880503/5000000000 : ℝ)|=(2637880503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-362676619/2500000000 : ℝ)|^4975 ≤ (2198983792491/25000000000000 : ℝ)^3951
        have hw : |(-362676619/2500000000 : ℝ)|=(362676619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444152927/10000000000 : ℝ)|^4975 ≤ (46503975824121/100000000000000 : ℝ)^3951
        have hw : |(5444152927/10000000000 : ℝ)|=(5444152927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_6 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42206087/80000000 : ℝ)*x 0 + (5444153093/10000000000 : ℝ)*x 1 + (-58028257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42206087/80000000 : ℝ)^4975 ≤ (44700087599647/100000000000000 : ℝ)^3951 := by
    have hnat : (42206087 : ℕ)^4975*100000000000000^3951 ≤ 44700087599647^3951*80000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42206087 80000000 44700087599647 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444153093/10000000000 : ℝ)^4975 ≤ (11625994402399/25000000000000 : ℝ)^3951 := by
    have hnat : (5444153093 : ℕ)^4975*25000000000000^3951 ≤ 11625994402399^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444153093 10000000000 11625994402399 25000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58028257/400000000 : ℝ)^4975 ≤ (4397967390299/50000000000000 : ℝ)^3951 := by
    have hnat : (58028257 : ℕ)^4975*50000000000000^3951 ≤ 4397967390299^3951*400000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58028257 400000000 4397967390299 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42206087/80000000 : ℝ), (5444153093/10000000000 : ℝ), (-58028257/400000000 : ℝ)] ![(44700087599647/100000000000000 : ℝ), (11625994402399/25000000000000 : ℝ), (4397967390299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42206087/80000000 : ℝ)|^4975 ≤ (44700087599647/100000000000000 : ℝ)^3951
        have hw : |(42206087/80000000 : ℝ)|=(42206087/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444153093/10000000000 : ℝ)|^4975 ≤ (11625994402399/25000000000000 : ℝ)^3951
        have hw : |(5444153093/10000000000 : ℝ)|=(5444153093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58028257/400000000 : ℝ)|^4975 ≤ (4397967390299/50000000000000 : ℝ)^3951
        have hw : |(-58028257/400000000 : ℝ)|=(58028257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1664_s2_7 (p : ℝ) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416993379/1000000000 : ℝ)*x 0 + (4522081897/10000000000 : ℝ)*x 1 + (3838065201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416993379/1000000000 : ℝ)^4975 ≤ (16620580165313/50000000000000 : ℝ)^3951 := by
    have hnat : (416993379 : ℕ)^4975*50000000000000^3951 ≤ 16620580165313^3951*1000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416993379 1000000000 16620580165313 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522081897/10000000000 : ℝ)^4975 ≤ (36813812522361/100000000000000 : ℝ)^3951 := by
    have hnat : (4522081897 : ℕ)^4975*100000000000000^3951 ≤ 36813812522361^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522081897 10000000000 36813812522361 100000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3838065201/10000000000 : ℝ)^4975 ≤ (14972513563503/50000000000000 : ℝ)^3951 := by
    have hnat : (3838065201 : ℕ)^4975*50000000000000^3951 ≤ 14972513563503^3951*10000000000^4975 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3838065201 10000000000 14972513563503 50000000000000 4975 3951 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4975/1024 : ℝ)) 4975 3951 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416993379/1000000000 : ℝ), (4522081897/10000000000 : ℝ), (3838065201/10000000000 : ℝ)] ![(16620580165313/50000000000000 : ℝ), (36813812522361/100000000000000 : ℝ), (14972513563503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416993379/1000000000 : ℝ)|^4975 ≤ (16620580165313/50000000000000 : ℝ)^3951
        have hw : |(416993379/1000000000 : ℝ)|=(416993379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522081897/10000000000 : ℝ)|^4975 ≤ (36813812522361/100000000000000 : ℝ)^3951
        have hw : |(4522081897/10000000000 : ℝ)|=(4522081897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3838065201/10000000000 : ℝ)|^4975 ≤ (14972513563503/50000000000000 : ℝ)^3951
        have hw : |(3838065201/10000000000 : ℝ)|=(3838065201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1664_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1071/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5343/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16301/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1071/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1071/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1071/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1071/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1071/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1071/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9939/100000 : ℝ) ^ (4971/1024 : ℝ) ≤ (271417546569571/20000000000000000000 : ℝ) := by
    have hpowers : (9939/100000 : ℝ)^4971 ≤ (271417546569571/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9939 : ℕ)^4971*20000000000000000000^1024 ≤ 271417546569571^1024*100000^4971 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9939 100000 271417546569571 20000000000000000000 4971 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9939/100000 : ℝ)) (X := (271417546569571/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1071/6250 : ℝ) ^ (4971/1024 : ℝ) ≤ (19099386928160633/100000000000000000000 : ℝ) := by
    have hpowers : (1071/6250 : ℝ)^4971 ≤ (19099386928160633/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1071 : ℕ)^4971*100000000000000000000^1024 ≤ 19099386928160633^1024*6250^4971 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1071 6250 19099386928160633 100000000000000000000 4971 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1071/6250 : ℝ)) (X := (19099386928160633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000271417546569571/10000000000000000000 : ℝ) ≤ (10000055909992543/10000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (10000271417546569571/10000000000000000000 : ℝ)^1024 ≤ (10000055909992543/10000000000000000 : ℝ)^4971 := by
      have hnat : (10000271417546569571 : ℕ)^1024*10000000000000000^4971 ≤ 10000055909992543^4971*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000271417546569571 10000000000000000000 10000055909992543 10000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055909992543/10000000000000000 : ℝ)) (X := (10000271417546569571/10000000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502557059332626061/12500000000000000000 : ℝ) ≤ (5000210679230163/5000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (12502557059332626061/12500000000000000000 : ℝ)^1024 ≤ (5000210679230163/5000000000000000 : ℝ)^4971 := by
      have hnat : (12502557059332626061 : ℕ)^1024*5000000000000000^4971 ≤ 5000210679230163^4971*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502557059332626061 12500000000000000000 5000210679230163 5000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000210679230163/5000000000000000 : ℝ)) (X := (12502557059332626061/12500000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019099386928160633/50000000000000000000 : ℝ) ≤ (10000786806928109/10000000000000000 : ℝ) ^ (4971/1024 : ℝ) := by
    have hpowers : (50019099386928160633/50000000000000000000 : ℝ)^1024 ≤ (10000786806928109/10000000000000000 : ℝ)^4971 := by
      have hnat : (50019099386928160633 : ℕ)^1024*10000000000000000^4971 ≤ 10000786806928109^4971*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019099386928160633 50000000000000000000 10000786806928109 10000000000000000 1024 4971 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000786806928109/10000000000000000 : ℝ)) (X := (50019099386928160633/50000000000000000000 : ℝ)) (by norm_num) 4971 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(271417546569571/20000000000000000000 : ℝ) ≤ ((23987712666524580499/23990000000000000000 : ℝ)+2*(365448467783/719700000000000 : ℝ)*(9939/100000 : ℝ))^(4971/1024 : ℝ) := by
    rw [show (23987712666524580499/23990000000000000000 : ℝ)+2*(365448467783/719700000000000 : ℝ)*(9939/100000 : ℝ)=(10000055909992543/10000000000000000 : ℝ) by norm_num, show 1+2*(271417546569571/20000000000000000000 : ℝ)=(10000271417546569571/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19099386928160633/100000000000000000000 : ℝ)+(271417546569571/20000000000000000000 : ℝ) ≤ ((23987712666524580499/23990000000000000000 : ℝ)+(365448467783/719700000000000 : ℝ)*((1071/6250 : ℝ)+(9939/100000 : ℝ)))^(4971/1024 : ℝ) := by
    rw [show (23987712666524580499/23990000000000000000 : ℝ)+(365448467783/719700000000000 : ℝ)*((1071/6250 : ℝ)+(9939/100000 : ℝ))=(5000210679230163/5000000000000000 : ℝ) by norm_num, show 1+(19099386928160633/100000000000000000000 : ℝ)+(271417546569571/20000000000000000000 : ℝ)=(12502557059332626061/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19099386928160633/100000000000000000000 : ℝ) ≤ ((23987712666524580499/23990000000000000000 : ℝ)+2*(365448467783/719700000000000 : ℝ)*(1071/6250 : ℝ))^(4971/1024 : ℝ) := by
    rw [show (23987712666524580499/23990000000000000000 : ℝ)+2*(365448467783/719700000000000 : ℝ)*(1071/6250 : ℝ)=(10000786806928109/10000000000000000 : ℝ) by norm_num, show 1+2*(19099386928160633/100000000000000000000 : ℝ)=(50019099386928160633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23987712666524580499/23990000000000000000 : ℝ)*(X 1 0+X 2 0)+(365448467783/719700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (9939/100000 : ℝ)) (hi := (1071/6250 : ℝ)) (c := (23987712666524580499/23990000000000000000 : ℝ)) (alpha := (365448467783/719700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23987712666524580499/23990000000000000000 : ℝ)*(X 0 1+X 2 1)+(365448467783/719700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (9939/100000 : ℝ)) (hi := (1071/6250 : ℝ)) (c := (23987712666524580499/23990000000000000000 : ℝ)) (alpha := (365448467783/719700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23987712666524580499/23990000000000000000 : ℝ)*(X 0 2+X 1 2)+(365448467783/719700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4971/1024 : ℝ)) (lo := (9939/100000 : ℝ)) (hi := (1071/6250 : ℝ)) (c := (23987712666524580499/23990000000000000000 : ℝ)) (alpha := (365448467783/719700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1576685311/10000000000 : ℝ)*X 0 0+(5446224437/10000000000 : ℝ)*X 0 1+(5182311169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336594277/2500000000 : ℝ)*X 1 0+(-1712548137/10000000000 : ℝ)*X 1 1+(5182311339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346377181/10000000000 : ℝ)*X 2 0+(323894449/625000000 : ℝ)*X 2 1+(-856274123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2084879723/5000000000 : ℝ)*X 0 0+(3832611227/10000000000 : ℝ)*X 0 1+(181099113/400000000 : ℝ)*X 0 2+(2084879723/5000000000 : ℝ)*X 1 0+(3832611227/10000000000 : ℝ)*X 1 1+(181099113/400000000 : ℝ)*X 1 2+(2084879723/5000000000 : ℝ)*X 2 0+(3832611227/10000000000 : ℝ)*X 2 1+(181099113/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1576751633/10000000000 : ℝ)*X 0 0+(259218031/500000000 : ℝ)*X 0 1+(85064889/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2637880503/5000000000 : ℝ)*X 1 0+(-362676619/2500000000 : ℝ)*X 1 1+(5444152927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42206087/80000000 : ℝ)*X 2 0+(5444153093/10000000000 : ℝ)*X 2 1+(-58028257/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((416993379/1000000000 : ℝ)*X 0 0+(4522081897/10000000000 : ℝ)*X 0 1+(3838065201/10000000000 : ℝ)*X 0 2+(416993379/1000000000 : ℝ)*X 1 0+(4522081897/10000000000 : ℝ)*X 1 1+(3838065201/10000000000 : ℝ)*X 1 2+(416993379/1000000000 : ℝ)*X 2 0+(4522081897/10000000000 : ℝ)*X 2 1+(3838065201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1664_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3216669200466386771599314961/599750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198652443/25000000000000 : ℝ)*(base19) + (815069239/100000000000000 : ℝ)*(base23) + (16722361/100000000000000 : ℝ)*(lower2) + (172349271/100000000000000 : ℝ)*(upper3) + (69758407/100000000000000 : ℝ)*(upper5) + (2614140014691513/100000000000000 : ℝ)*(major0) + (2614140014691513/100000000000000 : ℝ)*(major1) + (1307070007345757/50000000000000 : ℝ)*(major2) + (236820999960039/6250000000000 : ℝ)*(sp0) + (947286425716573/25000000000000 : ℝ)*(sp1) + (473643210300853/12500000000000 : ℝ)*(sp2) + (1439128751516267/100000000000000 : ℝ)*(sp3) + (131226443/1250000000000 : ℝ)*(sp4) + (920322471/20000000000000 : ℝ)*(sp7) + (719566676564311/50000000000000 : ℝ)*(f.failure) + (118410828046127/3125000000000 : ℝ)*(f.sum) + (130510488458419/71970000000000000000000000000 : ℝ)*base66 + (26425587957795985039/7197000000000000000000000000000000 : ℝ)*base68 + (5085478789430242743/1199500000000000000000000000000000 : ℝ)*base69 + (59348397861387985039/7197000000000000000000000000000000 : ℝ)*base72 + (30494095710341/71970000000000000000000000000 : ℝ)*base73 + (2111714680323757257/1199500000000000000000000000000000 : ℝ)*base76 + (4102257322314095013/2399000000000000000000000000000000 : ℝ)*base78 + (3779879663930095013/2399000000000000000000000000000000 : ℝ)*base80 + (5499827735477/11995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1666047/5000000000000000000000 : ℝ)*base90 + (1666047/5000000000000000000000 : ℝ)*base92 + (51666047/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4762938343847085707122702773/599750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (637766161/50000000000000 : ℝ)*(base19) + (243258051/20000000000000 : ℝ)*(base23) + (656501/6250000000000 : ℝ)*(upper2) + (199506287/100000000000000 : ℝ)*(upper3) + (8881857/5000000000000 : ℝ)*(upper5) + (2655590506293091/100000000000000 : ℝ)*(major0) + (2655590506293091/100000000000000 : ℝ)*(major1) + (2655590506293091/100000000000000 : ℝ)*(major2) + (3757418207/25000000000000 : ℝ)*(sp1) + (16256847049/100000000000000 : ℝ)*(sp2) + (1924614058897447/50000000000000 : ℝ)*(sp4) + (240575738286859/6250000000000 : ℝ)*(sp5) + (384921064465759/10000000000000 : ℝ)*(sp6) + (14619526300733/1000000000000 : ℝ)*(sp7) + (14619526300733/1000000000000 : ℝ)*(f.failure) + (1924614058897447/50000000000000 : ℝ)*(f.sum) + (23413844135723/35985000000000000000000000000 : ℝ)*base65 + (26427764630816397227/7197000000000000000000000000000000 : ℝ)*base67 + (8307994100151602773/7197000000000000000000000000000000 : ℝ)*base70 + (17190944052740397227/7197000000000000000000000000000000 : ℝ)*base71 + (92616546465053/35985000000000000000000000000 : ℝ)*base73 + (13655347329716397227/7197000000000000000000000000000000 : ℝ)*base75 + (22552448298233397227/7197000000000000000000000000000000 : ℝ)*base77 + (16036393410434397227/7197000000000000000000000000000000 : ℝ)*base79 + (100473384996307/35985000000000000000000000000 : ℝ)*base82 + (1021259/100000000000000000000 : ℝ)*base89 + (1021259/100000000000000000000 : ℝ)*base91 + (1021259/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1664_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1071/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5343/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1664_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1664_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5343/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1664_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1664_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1664_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4971/1024 : ℝ) ≤ p) (hpb : p ≤ (4975/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181646823/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5343/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1664_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

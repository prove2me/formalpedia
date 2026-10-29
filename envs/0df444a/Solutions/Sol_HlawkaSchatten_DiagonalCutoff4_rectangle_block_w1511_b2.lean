-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1511_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:36.524395+00:00
-- url     : https://prove2.me/submissions/b068a198-2e3a-4ed6-8550-1570117b4b13

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
theorem support_rectangle_w1511_s6_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869495429/10000000000 : ℝ)*x 0 + (2716682573/5000000000 : ℝ)*x 1 + (326099023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869495429/10000000000 : ℝ)^4519 ≤ (11437917302731/100000000000000 : ℝ)^3495 := by
    have hnat : (1869495429 : ℕ)^4519*100000000000000^3495 ≤ 11437917302731^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869495429 10000000000 11437917302731 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716682573/5000000000 : ℝ)^4519 ≤ (45440879776493/100000000000000 : ℝ)^3495 := by
    have hnat : (2716682573 : ℕ)^4519*100000000000000^3495 ≤ 45440879776493^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716682573 5000000000 45440879776493 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326099023/625000000 : ℝ)^4519 ≤ (10780300726241/25000000000000 : ℝ)^3495 := by
    have hnat : (326099023 : ℕ)^4519*25000000000000^3495 ≤ 10780300726241^3495*625000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326099023 625000000 10780300726241 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869495429/10000000000 : ℝ), (2716682573/5000000000 : ℝ), (326099023/625000000 : ℝ)] ![(11437917302731/100000000000000 : ℝ), (45440879776493/100000000000000 : ℝ), (10780300726241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869495429/10000000000 : ℝ)|^4519 ≤ (11437917302731/100000000000000 : ℝ)^3495
        have hw : |(-1869495429/10000000000 : ℝ)|=(1869495429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716682573/5000000000 : ℝ)|^4519 ≤ (45440879776493/100000000000000 : ℝ)^3495
        have hw : |(2716682573/5000000000 : ℝ)|=(2716682573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326099023/625000000 : ℝ)|^4519 ≤ (10780300726241/25000000000000 : ℝ)^3495
        have hw : |(326099023/625000000 : ℝ)|=(326099023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351646639/10000000000 : ℝ)*x 0 + (-79200407/400000000 : ℝ)*x 1 + (326099023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351646639/10000000000 : ℝ)^4519 ≤ (44559156991143/100000000000000 : ℝ)^3495 := by
    have hnat : (5351646639 : ℕ)^4519*100000000000000^3495 ≤ 44559156991143^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351646639 10000000000 44559156991143 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79200407/400000000 : ℝ)^4519 ≤ (12319640081543/100000000000000 : ℝ)^3495 := by
    have hnat : (79200407 : ℕ)^4519*100000000000000^3495 ≤ 12319640081543^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79200407 400000000 12319640081543 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326099023/625000000 : ℝ)^4519 ≤ (10780300726241/25000000000000 : ℝ)^3495 := by
    have hnat : (326099023 : ℕ)^4519*25000000000000^3495 ≤ 10780300726241^3495*625000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326099023 625000000 10780300726241 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351646639/10000000000 : ℝ), (-79200407/400000000 : ℝ), (326099023/625000000 : ℝ)] ![(44559156991143/100000000000000 : ℝ), (12319640081543/100000000000000 : ℝ), (10780300726241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351646639/10000000000 : ℝ)|^4519 ≤ (44559156991143/100000000000000 : ℝ)^3495
        have hw : |(5351646639/10000000000 : ℝ)|=(5351646639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79200407/400000000 : ℝ)|^4519 ≤ (12319640081543/100000000000000 : ℝ)^3495
        have hw : |(-79200407/400000000 : ℝ)|=(79200407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326099023/625000000 : ℝ)|^4519 ≤ (10780300726241/25000000000000 : ℝ)^3495
        have hw : |(326099023/625000000 : ℝ)|=(326099023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337911659/2500000000 : ℝ)*x 0 + (1669627/3200000 : ℝ)*x 1 + (-198001017/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337911659/2500000000 : ℝ)^4519 ≤ (22279578479423/50000000000000 : ℝ)^3495 := by
    have hnat : (1337911659 : ℕ)^4519*50000000000000^3495 ≤ 22279578479423^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337911659 2500000000 22279578479423 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669627/3200000 : ℝ)^4519 ≤ (21560601489883/50000000000000 : ℝ)^3495 := by
    have hnat : (1669627 : ℕ)^4519*50000000000000^3495 ≤ 21560601489883^3495*3200000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669627 3200000 21560601489883 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198001017/1000000000 : ℝ)^4519 ≤ (6159820020659/50000000000000 : ℝ)^3495 := by
    have hnat : (198001017 : ℕ)^4519*50000000000000^3495 ≤ 6159820020659^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198001017 1000000000 6159820020659 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337911659/2500000000 : ℝ), (1669627/3200000 : ℝ), (-198001017/1000000000 : ℝ)] ![(22279578479423/50000000000000 : ℝ), (21560601489883/50000000000000 : ℝ), (6159820020659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337911659/2500000000 : ℝ)|^4519 ≤ (22279578479423/50000000000000 : ℝ)^3495
        have hw : |(1337911659/2500000000 : ℝ)|=(1337911659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1669627/3200000 : ℝ)|^4519 ≤ (21560601489883/50000000000000 : ℝ)^3495
        have hw : |(1669627/3200000 : ℝ)|=(1669627/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198001017/1000000000 : ℝ)|^4519 ≤ (6159820020659/50000000000000 : ℝ)^3495
        have hw : |(-198001017/1000000000 : ℝ)|=(198001017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067559479/2500000000 : ℝ)*x 0 + (2015853203/5000000000 : ℝ)*x 1 + (4520662929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067559479/2500000000 : ℝ)^4519 ≤ (3327961016549/10000000000000 : ℝ)^3495 := by
    have hnat : (1067559479 : ℕ)^4519*10000000000000^3495 ≤ 3327961016549^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067559479 2500000000 3327961016549 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015853203/5000000000 : ℝ)^4519 ≤ (3861989687757/12500000000000 : ℝ)^3495 := by
    have hnat : (2015853203 : ℕ)^4519*12500000000000^3495 ≤ 3861989687757^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015853203 5000000000 3861989687757 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520662929/10000000000 : ℝ)^4519 ≤ (35824472321359/100000000000000 : ℝ)^3495 := by
    have hnat : (4520662929 : ℕ)^4519*100000000000000^3495 ≤ 35824472321359^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520662929 10000000000 35824472321359 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067559479/2500000000 : ℝ), (2015853203/5000000000 : ℝ), (4520662929/10000000000 : ℝ)] ![(3327961016549/10000000000000 : ℝ), (3861989687757/12500000000000 : ℝ), (35824472321359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067559479/2500000000 : ℝ)|^4519 ≤ (3327961016549/10000000000000 : ℝ)^3495
        have hw : |(1067559479/2500000000 : ℝ)|=(1067559479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015853203/5000000000 : ℝ)|^4519 ≤ (3861989687757/12500000000000 : ℝ)^3495
        have hw : |(2015853203/5000000000 : ℝ)|=(2015853203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520662929/10000000000 : ℝ)|^4519 ≤ (35824472321359/100000000000000 : ℝ)^3495
        have hw : |(4520662929/10000000000 : ℝ)|=(4520662929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934762219/5000000000 : ℝ)*x 0 + (652336861/1250000000 : ℝ)*x 1 + (1086449289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934762219/5000000000 : ℝ)^4519 ≤ (714884174139/6250000000000 : ℝ)^3495 := by
    have hnat : (934762219 : ℕ)^4519*6250000000000^3495 ≤ 714884174139^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934762219 5000000000 714884174139 6250000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652336861/1250000000 : ℝ)^4519 ≤ (862661406587/2000000000000 : ℝ)^3495 := by
    have hnat : (652336861 : ℕ)^4519*2000000000000^3495 ≤ 862661406587^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652336861 1250000000 862661406587 2000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086449289/2000000000 : ℝ)^4519 ≤ (45428782881079/100000000000000 : ℝ)^3495 := by
    have hnat : (1086449289 : ℕ)^4519*100000000000000^3495 ≤ 45428782881079^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086449289 2000000000 45428782881079 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934762219/5000000000 : ℝ), (652336861/1250000000 : ℝ), (1086449289/2000000000 : ℝ)] ![(714884174139/6250000000000 : ℝ), (862661406587/2000000000000 : ℝ), (45428782881079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934762219/5000000000 : ℝ)|^4519 ≤ (714884174139/6250000000000 : ℝ)^3495
        have hw : |(-934762219/5000000000 : ℝ)|=(934762219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652336861/1250000000 : ℝ)|^4519 ≤ (862661406587/2000000000000 : ℝ)^3495
        have hw : |(652336861/1250000000 : ℝ)|=(652336861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086449289/2000000000 : ℝ)|^4519 ≤ (45428782881079/100000000000000 : ℝ)^3495
        have hw : |(1086449289/2000000000 : ℝ)|=(1086449289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647505043/5000000000 : ℝ)*x 0 + (-1765348097/10000000000 : ℝ)*x 1 + (108644929/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647505043/5000000000 : ℝ)^4519 ≤ (43950369126807/100000000000000 : ℝ)^3495 := by
    have hnat : (2647505043 : ℕ)^4519*100000000000000^3495 ≤ 43950369126807^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647505043 5000000000 43950369126807 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1765348097/10000000000 : ℝ)^4519 ≤ (10620847911397/100000000000000 : ℝ)^3495 := by
    have hnat : (1765348097 : ℕ)^4519*100000000000000^3495 ≤ 10620847911397^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765348097 10000000000 10620847911397 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108644929/200000000 : ℝ)^4519 ≤ (5678597866893/12500000000000 : ℝ)^3495 := by
    have hnat : (108644929 : ℕ)^4519*12500000000000^3495 ≤ 5678597866893^3495*200000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108644929 200000000 5678597866893 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647505043/5000000000 : ℝ), (-1765348097/10000000000 : ℝ), (108644929/200000000 : ℝ)] ![(43950369126807/100000000000000 : ℝ), (10620847911397/100000000000000 : ℝ), (5678597866893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647505043/5000000000 : ℝ)|^4519 ≤ (43950369126807/100000000000000 : ℝ)^3495
        have hw : |(2647505043/5000000000 : ℝ)|=(2647505043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1765348097/10000000000 : ℝ)|^4519 ≤ (10620847911397/100000000000000 : ℝ)^3495
        have hw : |(-1765348097/10000000000 : ℝ)|=(1765348097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108644929/200000000 : ℝ)|^4519 ≤ (5678597866893/12500000000000 : ℝ)^3495
        have hw : |(108644929/200000000 : ℝ)|=(108644929/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295010093/10000000000 : ℝ)*x 0 + (1358061611/2500000000 : ℝ)*x 1 + (-1765348097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295010093/10000000000 : ℝ)^4519 ≤ (43950369201933/100000000000000 : ℝ)^3495 := by
    have hnat : (5295010093 : ℕ)^4519*100000000000000^3495 ≤ 43950369201933^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295010093 10000000000 43950369201933 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358061611/2500000000 : ℝ)^4519 ≤ (22714391435133/50000000000000 : ℝ)^3495 := by
    have hnat : (1358061611 : ℕ)^4519*50000000000000^3495 ≤ 22714391435133^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358061611 2500000000 22714391435133 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1765348097/10000000000 : ℝ)^4519 ≤ (10620847911397/100000000000000 : ℝ)^3495 := by
    have hnat : (1765348097 : ℕ)^4519*100000000000000^3495 ≤ 10620847911397^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765348097 10000000000 10620847911397 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295010093/10000000000 : ℝ), (1358061611/2500000000 : ℝ), (-1765348097/10000000000 : ℝ)] ![(43950369201933/100000000000000 : ℝ), (22714391435133/50000000000000 : ℝ), (10620847911397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295010093/10000000000 : ℝ)|^4519 ≤ (43950369201933/100000000000000 : ℝ)^3495
        have hw : |(5295010093/10000000000 : ℝ)|=(5295010093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358061611/2500000000 : ℝ)|^4519 ≤ (22714391435133/50000000000000 : ℝ)^3495
        have hw : |(1358061611/2500000000 : ℝ)|=(1358061611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1765348097/10000000000 : ℝ)|^4519 ≤ (10620847911397/100000000000000 : ℝ)^3495
        have hw : |(-1765348097/10000000000 : ℝ)|=(1765348097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s6_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270303653/10000000000 : ℝ)*x 0 + (4518146491/10000000000 : ℝ)*x 1 + (4034241373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270303653/10000000000 : ℝ)^4519 ≤ (8320068145893/25000000000000 : ℝ)^3495 := by
    have hnat : (4270303653 : ℕ)^4519*25000000000000^3495 ≤ 8320068145893^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270303653 10000000000 8320068145893 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518146491/10000000000 : ℝ)^4519 ≤ (7159737980609/20000000000000 : ℝ)^3495 := by
    have hnat : (4518146491 : ℕ)^4519*20000000000000^3495 ≤ 7159737980609^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518146491 10000000000 7159737980609 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034241373/10000000000 : ℝ)^4519 ≤ (7730259375939/25000000000000 : ℝ)^3495 := by
    have hnat : (4034241373 : ℕ)^4519*25000000000000^3495 ≤ 7730259375939^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034241373 10000000000 7730259375939 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270303653/10000000000 : ℝ), (4518146491/10000000000 : ℝ), (4034241373/10000000000 : ℝ)] ![(8320068145893/25000000000000 : ℝ), (7159737980609/20000000000000 : ℝ), (7730259375939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270303653/10000000000 : ℝ)|^4519 ≤ (8320068145893/25000000000000 : ℝ)^3495
        have hw : |(4270303653/10000000000 : ℝ)|=(4270303653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518146491/10000000000 : ℝ)|^4519 ≤ (7159737980609/20000000000000 : ℝ)^3495
        have hw : |(4518146491/10000000000 : ℝ)|=(4518146491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034241373/10000000000 : ℝ)|^4519 ≤ (7730259375939/25000000000000 : ℝ)^3495
        have hw : |(4034241373/10000000000 : ℝ)|=(4034241373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (341/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10911/100000 : ℝ) ^ (4517/1024 : ℝ) ≤ (5700235150682079/100000000000000000000 : ℝ) := by
    have hpowers : (10911/100000 : ℝ)^4517 ≤ (5700235150682079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10911 : ℕ)^4517*100000000000000000000^1024 ≤ 5700235150682079^1024*100000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10911 100000 5700235150682079 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10911/100000 : ℝ)) (X := (5700235150682079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4517/1024 : ℝ) ≤ (13344838241755107/50000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4517 ≤ (13344838241755107/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4517*50000000000000000000^1024 ≤ 13344838241755107^1024*100000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 13344838241755107 50000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (13344838241755107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005700235150682079/50000000000000000000 : ℝ) ≤ (10000258436285813/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50005700235150682079/50000000000000000000 : ℝ)^1024 ≤ (10000258436285813/10000000000000000 : ℝ)^4517 := by
      have hnat : (50005700235150682079 : ℕ)^1024*10000000000000000^4517 ≤ 10000258436285813^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005700235150682079 50000000000000000000 10000258436285813 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000258436285813/10000000000000000 : ℝ)) (X := (50005700235150682079/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032389911634192293/100000000000000000000 : ℝ) ≤ (10000734184560133/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (100032389911634192293/100000000000000000000 : ℝ)^1024 ≤ (10000734184560133/10000000000000000 : ℝ)^4517 := by
      have hnat : (100032389911634192293 : ℕ)^1024*10000000000000000^4517 ≤ 10000734184560133^4517*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032389911634192293 100000000000000000000 10000734184560133 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000734184560133/10000000000000000 : ℝ)) (X := (100032389911634192293/100000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013344838241755107/25000000000000000000 : ℝ) ≤ (10001209932834453/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (25013344838241755107/25000000000000000000 : ℝ)^1024 ≤ (10001209932834453/10000000000000000 : ℝ)^4517 := by
      have hnat : (25013344838241755107 : ℕ)^1024*10000000000000000^4517 ≤ 10001209932834453^4517*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013344838241755107 25000000000000000000 10001209932834453 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001209932834453/10000000000000000 : ℝ)) (X := (25013344838241755107/25000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5700235150682079/100000000000000000000 : ℝ) ≤ ((3809233315988043833/3810000000000000000 : ℝ)+2*(5946853429/5715000000000 : ℝ)*(10911/100000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (3809233315988043833/3810000000000000000 : ℝ)+2*(5946853429/5715000000000 : ℝ)*(10911/100000 : ℝ)=(10000258436285813/10000000000000000 : ℝ) by norm_num, show 1+2*(5700235150682079/100000000000000000000 : ℝ)=(50005700235150682079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13344838241755107/50000000000000000000 : ℝ)+(5700235150682079/100000000000000000000 : ℝ) ≤ ((3809233315988043833/3810000000000000000 : ℝ)+(5946853429/5715000000000 : ℝ)*((15483/100000 : ℝ)+(10911/100000 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (3809233315988043833/3810000000000000000 : ℝ)+(5946853429/5715000000000 : ℝ)*((15483/100000 : ℝ)+(10911/100000 : ℝ))=(10000734184560133/10000000000000000 : ℝ) by norm_num, show 1+(13344838241755107/50000000000000000000 : ℝ)+(5700235150682079/100000000000000000000 : ℝ)=(100032389911634192293/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13344838241755107/50000000000000000000 : ℝ) ≤ ((3809233315988043833/3810000000000000000 : ℝ)+2*(5946853429/5715000000000 : ℝ)*(15483/100000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (3809233315988043833/3810000000000000000 : ℝ)+2*(5946853429/5715000000000 : ℝ)*(15483/100000 : ℝ)=(10001209932834453/10000000000000000 : ℝ) by norm_num, show 1+2*(13344838241755107/50000000000000000000 : ℝ)=(25013344838241755107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3809233315988043833/3810000000000000000 : ℝ)*(X 1 0+X 2 0)+(5946853429/5715000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3809233315988043833/3810000000000000000 : ℝ)) (alpha := (5946853429/5715000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3809233315988043833/3810000000000000000 : ℝ)*(X 0 1+X 2 1)+(5946853429/5715000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3809233315988043833/3810000000000000000 : ℝ)) (alpha := (5946853429/5715000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3809233315988043833/3810000000000000000 : ℝ)*(X 0 2+X 1 2)+(5946853429/5715000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3809233315988043833/3810000000000000000 : ℝ)) (alpha := (5946853429/5715000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1869495429/10000000000 : ℝ)*X 0 0+(2716682573/5000000000 : ℝ)*X 0 1+(326099023/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351646639/10000000000 : ℝ)*X 1 0+(-79200407/400000000 : ℝ)*X 1 1+(326099023/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337911659/2500000000 : ℝ)*X 2 0+(1669627/3200000 : ℝ)*X 2 1+(-198001017/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1067559479/2500000000 : ℝ)*X 0 0+(2015853203/5000000000 : ℝ)*X 0 1+(4520662929/10000000000 : ℝ)*X 0 2+(1067559479/2500000000 : ℝ)*X 1 0+(2015853203/5000000000 : ℝ)*X 1 1+(4520662929/10000000000 : ℝ)*X 1 2+(1067559479/2500000000 : ℝ)*X 2 0+(2015853203/5000000000 : ℝ)*X 2 1+(4520662929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-934762219/5000000000 : ℝ)*X 0 0+(652336861/1250000000 : ℝ)*X 0 1+(1086449289/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647505043/5000000000 : ℝ)*X 1 0+(-1765348097/10000000000 : ℝ)*X 1 1+(108644929/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295010093/10000000000 : ℝ)*X 2 0+(1358061611/2500000000 : ℝ)*X 2 1+(-1765348097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4270303653/10000000000 : ℝ)*X 0 0+(4518146491/10000000000 : ℝ)*X 0 1+(4034241373/10000000000 : ℝ)*X 0 2+(4270303653/10000000000 : ℝ)*X 1 0+(4518146491/10000000000 : ℝ)*X 1 1+(4034241373/10000000000 : ℝ)*X 1 2+(4270303653/10000000000 : ℝ)*X 2 0+(4518146491/10000000000 : ℝ)*X 2 1+(4034241373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68040148706912319077481703/9525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31568193/2500000000000 : ℝ)*(base19) + (1174806001/100000000000000 : ℝ)*(base23) + (9132457/20000000000000 : ℝ)*(lower2) + (177935107/100000000000000 : ℝ)*(upper3) + (120061603/100000000000000 : ℝ)*(upper5) + (333978161873797/10000000000000 : ℝ)*(major0) + (333978161873797/10000000000000 : ℝ)*(major1) + (333978161873797/10000000000000 : ℝ)*(major2) + (579294201659113/12500000000000 : ℝ)*(sp0) + (4634372193536423/100000000000000 : ℝ)*(sp1) + (2317186140729071/50000000000000 : ℝ)*(sp2) + (1022590045445973/50000000000000 : ℝ)*(sp3) + (19842991239/100000000000000 : ℝ)*(sp4) + (9452209087/100000000000000 : ℝ)*(sp7) + (1022594771550517/50000000000000 : ℝ)*(f.failure) + (4634373456264143/100000000000000 : ℝ)*(f.sum) + (1417588425887/1143000000000000000000000000 : ℝ)*base66 + (298847231652268297/114300000000000000000000000000000 : ℝ)*base68 + (256959288085168297/114300000000000000000000000000000 : ℝ)*base70 + (199805325532768297/114300000000000000000000000000000 : ℝ)*base72 + (77128513981/71437500000000000000000000 : ℝ)*base73 + (694862663394268297/114300000000000000000000000000000 : ℝ)*base76 + (786973342647268297/114300000000000000000000000000000 : ℝ)*base78 + (1674217538161531703/114300000000000000000000000000000 : ℝ)*base79 + (369510836957/228600000000000000000000000 : ℝ)*base81 + (77723773/5000000000000000000000 : ℝ)*base89 + (77723773/5000000000000000000000 : ℝ)*base91 + (77723773/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75588076469920900452126721/7620000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1619965099/100000000000000 : ℝ)*(base19) + (1766365571/100000000000000 : ℝ)*(base23) + (268160833/50000000000000 : ℝ)*(lower1) + (41195961/20000000000000 : ℝ)*(upper3) + (31793079/50000000000000 : ℝ)*(lower4) + (20858247/10000000000000 : ℝ)*(upper5) + (134983871111779/4000000000000 : ℝ)*(major0) + (134983871111779/4000000000000 : ℝ)*(major1) + (134983871111779/4000000000000 : ℝ)*(major2) + (470330659/25000000000000 : ℝ)*(sp2) + (117067096124403/2500000000000 : ℝ)*(sp4) + (234134111250551/5000000000000 : ℝ)*(sp5) + (585335024660989/12500000000000 : ℝ)*(sp6) + (413301875991263/20000000000000 : ℝ)*(sp7) + (413301875991263/20000000000000 : ℝ)*(f.failure) + (117067096124403/2500000000000 : ℝ)*(f.sum) + (384196130159/228600000000000000000000000 : ℝ)*base65 + (1219627747578826721/45720000000000000000000000000000 : ℝ)*base67 + (169492095613573279/45720000000000000000000000000000 : ℝ)*base70 + (557213812827973279/45720000000000000000000000000000 : ℝ)*base72 + (75454715303/45720000000000000000000000 : ℝ)*base74 + (1798312157245573279/45720000000000000000000000000000 : ℝ)*base76 + (58216615894213279/45720000000000000000000000000000 : ℝ)*base78 + (469475802053866721/45720000000000000000000000000000 : ℝ)*base79 + (2085932466173/1143000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2586953/2000000000000000000000 : ℝ)*base90 + (2586953/2000000000000000000000 : ℝ)*base92 + (2586953/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1511_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1511_box_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655686573/10000000000 : ℝ)*x 0 + (1080588429/2000000000 : ℝ)*x 1 + (1080588397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655686573/10000000000 : ℝ)^4519 ≤ (1221958769247/12500000000000 : ℝ)^3495 := by
    have hnat : (1655686573 : ℕ)^4519*12500000000000^3495 ≤ 1221958769247^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655686573 10000000000 1221958769247 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080588429/2000000000 : ℝ)^4519 ≤ (1409755180643/3125000000000 : ℝ)^3495 := by
    have hnat : (1080588429 : ℕ)^4519*3125000000000^3495 ≤ 1409755180643^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080588429 2000000000 1409755180643 3125000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080588397/2000000000 : ℝ)^4519 ≤ (22556082026617/50000000000000 : ℝ)^3495 := by
    have hnat : (1080588397 : ℕ)^4519*50000000000000^3495 ≤ 22556082026617^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080588397 2000000000 22556082026617 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655686573/10000000000 : ℝ), (1080588429/2000000000 : ℝ), (1080588397/2000000000 : ℝ)] ![(1221958769247/12500000000000 : ℝ), (1409755180643/3125000000000 : ℝ), (22556082026617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655686573/10000000000 : ℝ)|^4519 ≤ (1221958769247/12500000000000 : ℝ)^3495
        have hw : |(-1655686573/10000000000 : ℝ)|=(1655686573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080588429/2000000000 : ℝ)|^4519 ≤ (1409755180643/3125000000000 : ℝ)^3495
        have hw : |(1080588429/2000000000 : ℝ)|=(1080588429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080588397/2000000000 : ℝ)|^4519 ≤ (22556082026617/50000000000000 : ℝ)^3495
        have hw : |(1080588397/2000000000 : ℝ)|=(1080588397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658845447/1250000000 : ℝ)*x 0 + (-57469761/312500000 : ℝ)*x 1 + (33768389/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658845447/1250000000 : ℝ)^4519 ≤ (43690324199471/100000000000000 : ℝ)^3495 := by
    have hnat : (658845447 : ℕ)^4519*100000000000000^3495 ≤ 43690324199471^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658845447 1250000000 43690324199471 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57469761/312500000 : ℝ)^4519 ≤ (11197508974723/100000000000000 : ℝ)^3495 := by
    have hnat : (57469761 : ℕ)^4519*100000000000000^3495 ≤ 11197508974723^3495*312500000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57469761 312500000 11197508974723 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33768389/62500000 : ℝ)^4519 ≤ (22556083403093/50000000000000 : ℝ)^3495 := by
    have hnat : (33768389 : ℕ)^4519*50000000000000^3495 ≤ 22556083403093^3495*62500000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33768389 62500000 22556083403093 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658845447/1250000000 : ℝ), (-57469761/312500000 : ℝ), (33768389/62500000 : ℝ)] ![(43690324199471/100000000000000 : ℝ), (11197508974723/100000000000000 : ℝ), (22556083403093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658845447/1250000000 : ℝ)|^4519 ≤ (43690324199471/100000000000000 : ℝ)^3495
        have hw : |(658845447/1250000000 : ℝ)|=(658845447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57469761/312500000 : ℝ)|^4519 ≤ (11197508974723/100000000000000 : ℝ)^3495
        have hw : |(-57469761/312500000 : ℝ)|=(57469761/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33768389/62500000 : ℝ)|^4519 ≤ (22556083403093/50000000000000 : ℝ)^3495
        have hw : |(33768389/62500000 : ℝ)|=(33768389/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270763259/10000000000 : ℝ)*x 0 + (5402942387/10000000000 : ℝ)*x 1 + (-919516291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270763259/10000000000 : ℝ)^4519 ≤ (21845160400959/50000000000000 : ℝ)^3495 := by
    have hnat : (5270763259 : ℕ)^4519*50000000000000^3495 ≤ 21845160400959^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270763259 10000000000 21845160400959 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402942387/10000000000 : ℝ)^4519 ≤ (22556084196591/50000000000000 : ℝ)^3495 := by
    have hnat : (5402942387 : ℕ)^4519*50000000000000^3495 ≤ 22556084196591^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402942387 10000000000 22556084196591 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919516291/5000000000 : ℝ)^4519 ≤ (5598755392729/50000000000000 : ℝ)^3495 := by
    have hnat : (919516291 : ℕ)^4519*50000000000000^3495 ≤ 5598755392729^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919516291 5000000000 5598755392729 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270763259/10000000000 : ℝ), (5402942387/10000000000 : ℝ), (-919516291/5000000000 : ℝ)] ![(21845160400959/50000000000000 : ℝ), (22556084196591/50000000000000 : ℝ), (5598755392729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270763259/10000000000 : ℝ)|^4519 ≤ (21845160400959/50000000000000 : ℝ)^3495
        have hw : |(5270763259/10000000000 : ℝ)|=(5270763259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402942387/10000000000 : ℝ)|^4519 ≤ (22556084196591/50000000000000 : ℝ)^3495
        have hw : |(5402942387/10000000000 : ℝ)|=(5402942387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919516291/5000000000 : ℝ)|^4519 ≤ (5598755392729/50000000000000 : ℝ)^3495
        have hw : |(-919516291/5000000000 : ℝ)|=(919516291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4473349659/10000000000 : ℝ)*x 0 + (2087835551/5000000000 : ℝ)*x 1 + (4175670599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4473349659/10000000000 : ℝ)^4519 ≤ (2208776565991/6250000000000 : ℝ)^3495 := by
    have hnat : (4473349659 : ℕ)^4519*6250000000000^3495 ≤ 2208776565991^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473349659 10000000000 2208776565991 6250000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087835551/5000000000 : ℝ)^4519 ≤ (32329789981037/100000000000000 : ℝ)^3495 := by
    have hnat : (2087835551 : ℕ)^4519*100000000000000^3495 ≤ 32329789981037^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087835551 5000000000 32329789981037 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4175670599/10000000000 : ℝ)^4519 ≤ (3232978494557/10000000000000 : ℝ)^3495 := by
    have hnat : (4175670599 : ℕ)^4519*10000000000000^3495 ≤ 3232978494557^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175670599 10000000000 3232978494557 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4473349659/10000000000 : ℝ), (2087835551/5000000000 : ℝ), (4175670599/10000000000 : ℝ)] ![(2208776565991/6250000000000 : ℝ), (32329789981037/100000000000000 : ℝ), (3232978494557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4473349659/10000000000 : ℝ)|^4519 ≤ (2208776565991/6250000000000 : ℝ)^3495
        have hw : |(4473349659/10000000000 : ℝ)|=(4473349659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2087835551/5000000000 : ℝ)|^4519 ≤ (32329789981037/100000000000000 : ℝ)^3495
        have hw : |(2087835551/5000000000 : ℝ)|=(2087835551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4175670599/10000000000 : ℝ)|^4519 ≤ (3232978494557/10000000000000 : ℝ)^3495
        have hw : |(4175670599/10000000000 : ℝ)|=(4175670599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044372523/5000000000 : ℝ)*x 0 + (5243591357/10000000000 : ℝ)*x 1 + (2621795941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044372523/5000000000 : ℝ)^4519 ≤ (13201360035611/100000000000000 : ℝ)^3495 := by
    have hnat : (1044372523 : ℕ)^4519*100000000000000^3495 ≤ 13201360035611^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044372523 5000000000 13201360035611 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243591357/10000000000 : ℝ)^4519 ≤ (21699658582699/50000000000000 : ℝ)^3495 := by
    have hnat : (5243591357 : ℕ)^4519*50000000000000^3495 ≤ 21699658582699^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243591357 10000000000 21699658582699 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621795941/5000000000 : ℝ)^4519 ≤ (8679864556749/20000000000000 : ℝ)^3495 := by
    have hnat : (2621795941 : ℕ)^4519*20000000000000^3495 ≤ 8679864556749^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621795941 5000000000 8679864556749 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044372523/5000000000 : ℝ), (5243591357/10000000000 : ℝ), (2621795941/5000000000 : ℝ)] ![(13201360035611/100000000000000 : ℝ), (21699658582699/50000000000000 : ℝ), (8679864556749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044372523/5000000000 : ℝ)|^4519 ≤ (13201360035611/100000000000000 : ℝ)^3495
        have hw : |(-1044372523/5000000000 : ℝ)|=(1044372523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243591357/10000000000 : ℝ)|^4519 ≤ (21699658582699/50000000000000 : ℝ)^3495
        have hw : |(5243591357/10000000000 : ℝ)|=(5243591357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621795941/5000000000 : ℝ)|^4519 ≤ (8679864556749/20000000000000 : ℝ)^3495
        have hw : |(2621795941/5000000000 : ℝ)|=(2621795941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690857821/5000000000 : ℝ)*x 0 + (-952372983/5000000000 : ℝ)*x 1 + (655448939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690857821/5000000000 : ℝ)^4519 ≤ (44883138762837/100000000000000 : ℝ)^3495 := by
    have hnat : (2690857821 : ℕ)^4519*100000000000000^3495 ≤ 44883138762837^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690857821 5000000000 44883138762837 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952372983/5000000000 : ℝ)^4519 ≤ (5858771200143/50000000000000 : ℝ)^3495 := by
    have hnat : (952372983 : ℕ)^4519*50000000000000^3495 ≤ 5858771200143^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952372983 5000000000 5858771200143 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655448939/1250000000 : ℝ)^4519 ≤ (10849829706037/25000000000000 : ℝ)^3495 := by
    have hnat : (655448939 : ℕ)^4519*25000000000000^3495 ≤ 10849829706037^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655448939 1250000000 10849829706037 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690857821/5000000000 : ℝ), (-952372983/5000000000 : ℝ), (655448939/1250000000 : ℝ)] ![(44883138762837/100000000000000 : ℝ), (5858771200143/50000000000000 : ℝ), (10849829706037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690857821/5000000000 : ℝ)|^4519 ≤ (44883138762837/100000000000000 : ℝ)^3495
        have hw : |(2690857821/5000000000 : ℝ)|=(2690857821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-952372983/5000000000 : ℝ)|^4519 ≤ (5858771200143/50000000000000 : ℝ)^3495
        have hw : |(-952372983/5000000000 : ℝ)|=(952372983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655448939/1250000000 : ℝ)|^4519 ≤ (10849829706037/25000000000000 : ℝ)^3495
        have hw : |(655448939/1250000000 : ℝ)|=(655448939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381715601/10000000000 : ℝ)*x 0 + (131089793/250000000 : ℝ)*x 1 + (-1904745741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381715601/10000000000 : ℝ)^4519 ≤ (11220784580179/25000000000000 : ℝ)^3495 := by
    have hnat : (5381715601 : ℕ)^4519*25000000000000^3495 ≤ 11220784580179^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381715601 10000000000 11220784580179 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131089793/250000000 : ℝ)^4519 ≤ (43399321050083/100000000000000 : ℝ)^3495 := by
    have hnat : (131089793 : ℕ)^4519*100000000000000^3495 ≤ 43399321050083^3495*250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131089793 250000000 43399321050083 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904745741/10000000000 : ℝ)^4519 ≤ (11717540610599/100000000000000 : ℝ)^3495 := by
    have hnat : (1904745741 : ℕ)^4519*100000000000000^3495 ≤ 11717540610599^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904745741 10000000000 11717540610599 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381715601/10000000000 : ℝ), (131089793/250000000 : ℝ), (-1904745741/10000000000 : ℝ)] ![(11220784580179/25000000000000 : ℝ), (43399321050083/100000000000000 : ℝ), (11717540610599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381715601/10000000000 : ℝ)|^4519 ≤ (11220784580179/25000000000000 : ℝ)^3495
        have hw : |(5381715601/10000000000 : ℝ)|=(5381715601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131089793/250000000 : ℝ)|^4519 ≤ (43399321050083/100000000000000 : ℝ)^3495
        have hw : |(131089793/250000000 : ℝ)|=(131089793/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904745741/10000000000 : ℝ)|^4519 ≤ (11717540610599/100000000000000 : ℝ)^3495
        have hw : |(-1904745741/10000000000 : ℝ)|=(1904745741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2032355987/5000000000 : ℝ)*x 0 + (2189927479/5000000000 : ℝ)*x 1 + (437985557/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032355987/5000000000 : ℝ)^4519 ≤ (31223344208347/100000000000000 : ℝ)^3495 := by
    have hnat : (2032355987 : ℕ)^4519*100000000000000^3495 ≤ 31223344208347^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032355987 5000000000 31223344208347 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189927479/5000000000 : ℝ)^4519 ≤ (17194162392461/50000000000000 : ℝ)^3495 := by
    have hnat : (2189927479 : ℕ)^4519*50000000000000^3495 ≤ 17194162392461^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189927479 5000000000 17194162392461 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437985557/1000000000 : ℝ)^4519 ≤ (2149270687367/6250000000000 : ℝ)^3495 := by
    have hnat : (437985557 : ℕ)^4519*6250000000000^3495 ≤ 2149270687367^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437985557 1000000000 2149270687367 6250000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2032355987/5000000000 : ℝ), (2189927479/5000000000 : ℝ), (437985557/1000000000 : ℝ)] ![(31223344208347/100000000000000 : ℝ), (17194162392461/50000000000000 : ℝ), (2149270687367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2032355987/5000000000 : ℝ)|^4519 ≤ (31223344208347/100000000000000 : ℝ)^3495
        have hw : |(2032355987/5000000000 : ℝ)|=(2032355987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2189927479/5000000000 : ℝ)|^4519 ≤ (17194162392461/50000000000000 : ℝ)^3495
        have hw : |(2189927479/5000000000 : ℝ)|=(2189927479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(437985557/1000000000 : ℝ)|^4519 ≤ (2149270687367/6250000000000 : ℝ)^3495
        have hw : |(437985557/1000000000 : ℝ)|=(437985557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_8 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1997234611/10000000000 : ℝ)*x 0 + (10023369/19531250 : ℝ)*x 1 + (271169933/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997234611/10000000000 : ℝ)^4519 ≤ (2491677361651/20000000000000 : ℝ)^3495 := by
    have hnat : (1997234611 : ℕ)^4519*20000000000000^3495 ≤ 2491677361651^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997234611 10000000000 2491677361651 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10023369/19531250 : ℝ)^4519 ≤ (42208478683743/100000000000000 : ℝ)^3495 := by
    have hnat : (10023369 : ℕ)^4519*100000000000000^3495 ≤ 42208478683743^3495*19531250^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10023369 19531250 42208478683743 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271169933/500000000 : ℝ)^4519 ≤ (9066626897409/20000000000000 : ℝ)^3495 := by
    have hnat : (271169933 : ℕ)^4519*20000000000000^3495 ≤ 9066626897409^3495*500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271169933 500000000 9066626897409 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1997234611/10000000000 : ℝ), (10023369/19531250 : ℝ), (271169933/500000000 : ℝ)] ![(2491677361651/20000000000000 : ℝ), (42208478683743/100000000000000 : ℝ), (9066626897409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1997234611/10000000000 : ℝ)|^4519 ≤ (2491677361651/20000000000000 : ℝ)^3495
        have hw : |(-1997234611/10000000000 : ℝ)|=(1997234611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10023369/19531250 : ℝ)|^4519 ≤ (42208478683743/100000000000000 : ℝ)^3495
        have hw : |(10023369/19531250 : ℝ)|=(10023369/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271169933/500000000 : ℝ)|^4519 ≤ (9066626897409/20000000000000 : ℝ)^3495
        have hw : |(271169933/500000000 : ℝ)|=(271169933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_9 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628257123/5000000000 : ℝ)*x 0 + (-1830350201/10000000000 : ℝ)*x 1 + (2711699279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628257123/5000000000 : ℝ)^4519 ≤ (5442207852021/12500000000000 : ℝ)^3495 := by
    have hnat : (2628257123 : ℕ)^4519*12500000000000^3495 ≤ 5442207852021^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628257123 5000000000 5442207852021 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830350201/10000000000 : ℝ)^4519 ≤ (2782300944563/25000000000000 : ℝ)^3495 := by
    have hnat : (1830350201 : ℕ)^4519*25000000000000^3495 ≤ 2782300944563^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830350201 10000000000 2782300944563 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711699279/5000000000 : ℝ)^4519 ≤ (11333283346161/25000000000000 : ℝ)^3495 := by
    have hnat : (2711699279 : ℕ)^4519*25000000000000^3495 ≤ 11333283346161^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711699279 5000000000 11333283346161 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628257123/5000000000 : ℝ), (-1830350201/10000000000 : ℝ), (2711699279/5000000000 : ℝ)] ![(5442207852021/12500000000000 : ℝ), (2782300944563/25000000000000 : ℝ), (11333283346161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628257123/5000000000 : ℝ)|^4519 ≤ (5442207852021/12500000000000 : ℝ)^3495
        have hw : |(2628257123/5000000000 : ℝ)|=(2628257123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1830350201/10000000000 : ℝ)|^4519 ≤ (2782300944563/25000000000000 : ℝ)^3495
        have hw : |(-1830350201/10000000000 : ℝ)|=(1830350201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711699279/5000000000 : ℝ)|^4519 ≤ (11333283346161/25000000000000 : ℝ)^3495
        have hw : |(2711699279/5000000000 : ℝ)|=(2711699279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_10 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314128609/2500000000 : ℝ)*x 0 + (5423398177/10000000000 : ℝ)*x 1 + (-1830350467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314128609/2500000000 : ℝ)^4519 ≤ (43537664850941/100000000000000 : ℝ)^3495 := by
    have hnat : (1314128609 : ℕ)^4519*100000000000000^3495 ≤ 43537664850941^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314128609 2500000000 43537664850941 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423398177/10000000000 : ℝ)^4519 ≤ (45333129266853/100000000000000 : ℝ)^3495 := by
    have hnat : (5423398177 : ℕ)^4519*100000000000000^3495 ≤ 45333129266853^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423398177 10000000000 45333129266853 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1830350467/10000000000 : ℝ)^4519 ≤ (5564602934753/50000000000000 : ℝ)^3495 := by
    have hnat : (1830350467 : ℕ)^4519*50000000000000^3495 ≤ 5564602934753^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830350467 10000000000 5564602934753 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314128609/2500000000 : ℝ), (5423398177/10000000000 : ℝ), (-1830350467/10000000000 : ℝ)] ![(43537664850941/100000000000000 : ℝ), (45333129266853/100000000000000 : ℝ), (5564602934753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314128609/2500000000 : ℝ)|^4519 ≤ (43537664850941/100000000000000 : ℝ)^3495
        have hw : |(1314128609/2500000000 : ℝ)|=(1314128609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423398177/10000000000 : ℝ)|^4519 ≤ (45333129266853/100000000000000 : ℝ)^3495
        have hw : |(5423398177/10000000000 : ℝ)|=(5423398177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1830350467/10000000000 : ℝ)|^4519 ≤ (5564602934753/50000000000000 : ℝ)^3495
        have hw : |(-1830350467/10000000000 : ℝ)|=(1830350467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_11 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (180986267/400000000 : ℝ)*x 0 + (1037356547/2500000000 : ℝ)*x 1 + (829885337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180986267/400000000 : ℝ)^4519 ≤ (35865399279631/100000000000000 : ℝ)^3495 := by
    have hnat : (180986267 : ℕ)^4519*100000000000000^3495 ≤ 35865399279631^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180986267 400000000 35865399279631 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037356547/2500000000 : ℝ)^4519 ≤ (32067297867713/100000000000000 : ℝ)^3495 := by
    have hnat : (1037356547 : ℕ)^4519*100000000000000^3495 ≤ 32067297867713^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037356547 2500000000 32067297867713 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829885337/2000000000 : ℝ)^4519 ≤ (8016825708483/25000000000000 : ℝ)^3495 := by
    have hnat : (829885337 : ℕ)^4519*25000000000000^3495 ≤ 8016825708483^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829885337 2000000000 8016825708483 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180986267/400000000 : ℝ), (1037356547/2500000000 : ℝ), (829885337/2000000000 : ℝ)] ![(35865399279631/100000000000000 : ℝ), (32067297867713/100000000000000 : ℝ), (8016825708483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180986267/400000000 : ℝ)|^4519 ≤ (35865399279631/100000000000000 : ℝ)^3495
        have hw : |(180986267/400000000 : ℝ)|=(180986267/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037356547/2500000000 : ℝ)|^4519 ≤ (32067297867713/100000000000000 : ℝ)^3495
        have hw : |(1037356547/2500000000 : ℝ)|=(1037356547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829885337/2000000000 : ℝ)|^4519 ≤ (8016825708483/25000000000000 : ℝ)^3495
        have hw : |(829885337/2000000000 : ℝ)|=(829885337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_12 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1747152109/10000000000 : ℝ)*x 0 + (5510977003/10000000000 : ℝ)*x 1 + (2614282831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1747152109/10000000000 : ℝ)^4519 ≤ (5239757749847/50000000000000 : ℝ)^3495 := by
    have hnat : (1747152109 : ℕ)^4519*50000000000000^3495 ≤ 5239757749847^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747152109 10000000000 5239757749847 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510977003/10000000000 : ℝ)^4519 ≤ (4628189892951/10000000000000 : ℝ)^3495 := by
    have hnat : (5510977003 : ℕ)^4519*10000000000000^3495 ≤ 4628189892951^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510977003 10000000000 4628189892951 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614282831/5000000000 : ℝ)^4519 ≤ (43238585547877/100000000000000 : ℝ)^3495 := by
    have hnat : (2614282831 : ℕ)^4519*100000000000000^3495 ≤ 43238585547877^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614282831 5000000000 43238585547877 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1747152109/10000000000 : ℝ), (5510977003/10000000000 : ℝ), (2614282831/5000000000 : ℝ)] ![(5239757749847/50000000000000 : ℝ), (4628189892951/10000000000000 : ℝ), (43238585547877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1747152109/10000000000 : ℝ)|^4519 ≤ (5239757749847/50000000000000 : ℝ)^3495
        have hw : |(-1747152109/10000000000 : ℝ)|=(1747152109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510977003/10000000000 : ℝ)|^4519 ≤ (4628189892951/10000000000000 : ℝ)^3495
        have hw : |(5510977003/10000000000 : ℝ)|=(5510977003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614282831/5000000000 : ℝ)|^4519 ≤ (43238585547877/100000000000000 : ℝ)^3495
        have hw : |(2614282831/5000000000 : ℝ)|=(2614282831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_13 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392177353/10000000000 : ℝ)*x 0 + (-119422717/625000000 : ℝ)*x 1 + (26142829/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392177353/10000000000 : ℝ)^4519 ≤ (562449802347/1250000000000 : ℝ)^3495 := by
    have hnat : (5392177353 : ℕ)^4519*1250000000000^3495 ≤ 562449802347^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392177353 10000000000 562449802347 1250000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119422717/625000000 : ℝ)^4519 ≤ (2941357193877/25000000000000 : ℝ)^3495 := by
    have hnat : (119422717 : ℕ)^4519*25000000000000^3495 ≤ 2941357193877^3495*625000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119422717 625000000 2941357193877 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26142829/50000000 : ℝ)^4519 ≤ (21619293511729/50000000000000 : ℝ)^3495 := by
    have hnat : (26142829 : ℕ)^4519*50000000000000^3495 ≤ 21619293511729^3495*50000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26142829 50000000 21619293511729 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392177353/10000000000 : ℝ), (-119422717/625000000 : ℝ), (26142829/50000000 : ℝ)] ![(562449802347/1250000000000 : ℝ), (2941357193877/25000000000000 : ℝ), (21619293511729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392177353/10000000000 : ℝ)|^4519 ≤ (562449802347/1250000000000 : ℝ)^3495
        have hw : |(5392177353/10000000000 : ℝ)|=(5392177353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119422717/625000000 : ℝ)|^4519 ≤ (2941357193877/25000000000000 : ℝ)^3495
        have hw : |(-119422717/625000000 : ℝ)|=(119422717/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26142829/50000000 : ℝ)|^4519 ≤ (21619293511729/50000000000000 : ℝ)^3495
        have hw : |(26142829/50000000 : ℝ)|=(26142829/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_14 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392177359/10000000000 : ℝ)*x 0 + (1045713141/2000000000 : ℝ)*x 1 + (-1910763591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392177359/10000000000 : ℝ)^4519 ≤ (44995984252497/100000000000000 : ℝ)^3495 := by
    have hnat : (5392177359 : ℕ)^4519*100000000000000^3495 ≤ 44995984252497^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392177359 10000000000 44995984252497 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045713141/2000000000 : ℝ)^4519 ≤ (2161929300383/5000000000000 : ℝ)^3495 := by
    have hnat : (1045713141 : ℕ)^4519*5000000000000^3495 ≤ 2161929300383^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045713141 2000000000 2161929300383 5000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910763591/10000000000 : ℝ)^4519 ≤ (11765429722929/100000000000000 : ℝ)^3495 := by
    have hnat : (1910763591 : ℕ)^4519*100000000000000^3495 ≤ 11765429722929^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910763591 10000000000 11765429722929 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392177359/10000000000 : ℝ), (1045713141/2000000000 : ℝ), (-1910763591/10000000000 : ℝ)] ![(44995984252497/100000000000000 : ℝ), (2161929300383/5000000000000 : ℝ), (11765429722929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392177359/10000000000 : ℝ)|^4519 ≤ (44995984252497/100000000000000 : ℝ)^3495
        have hw : |(5392177359/10000000000 : ℝ)|=(5392177359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045713141/2000000000 : ℝ)|^4519 ≤ (2161929300383/5000000000000 : ℝ)^3495
        have hw : |(1045713141/2000000000 : ℝ)|=(1045713141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1910763591/10000000000 : ℝ)|^4519 ≤ (11765429722929/100000000000000 : ℝ)^3495
        have hw : |(-1910763591/10000000000 : ℝ)|=(1910763591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_box_15 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4025318347/10000000000 : ℝ)*x 0 + (175963471/400000000 : ℝ)*x 1 + (17183927/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4025318347/10000000000 : ℝ)^4519 ≤ (30832636197681/100000000000000 : ℝ)^3495 := by
    have hnat : (4025318347 : ℕ)^4519*100000000000000^3495 ≤ 30832636197681^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025318347 10000000000 30832636197681 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175963471/400000000 : ℝ)^4519 ≤ (17291844665849/50000000000000 : ℝ)^3495 := by
    have hnat : (175963471 : ℕ)^4519*50000000000000^3495 ≤ 17291844665849^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175963471 400000000 17291844665849 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17183927/39062500 : ℝ)^4519 ≤ (17291837230211/50000000000000 : ℝ)^3495 := by
    have hnat : (17183927 : ℕ)^4519*50000000000000^3495 ≤ 17291837230211^3495*39062500^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17183927 39062500 17291837230211 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4025318347/10000000000 : ℝ), (175963471/400000000 : ℝ), (17183927/39062500 : ℝ)] ![(30832636197681/100000000000000 : ℝ), (17291844665849/50000000000000 : ℝ), (17291837230211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4025318347/10000000000 : ℝ)|^4519 ≤ (30832636197681/100000000000000 : ℝ)^3495
        have hw : |(4025318347/10000000000 : ℝ)|=(4025318347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175963471/400000000 : ℝ)|^4519 ≤ (17291844665849/50000000000000 : ℝ)^3495
        have hw : |(175963471/400000000 : ℝ)|=(175963471/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17183927/39062500 : ℝ)|^4519 ≤ (17291837230211/50000000000000 : ℝ)^3495
        have hw : |(17183927/39062500 : ℝ)|=(17183927/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(31869/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58623/100000 : ℝ) ∧ (20077/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17199/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (341/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (341/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (341/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (341/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (341/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (341/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (341/3125 : ℝ) ^ (4517/1024 : ℝ) ≤ (2851270009815161/50000000000000000000 : ℝ) := by
    have hpowers : (341/3125 : ℝ)^4517 ≤ (2851270009815161/50000000000000000000 : ℝ)^1024 := by
      have hnat : (341 : ℕ)^4517*50000000000000000000^1024 ≤ 2851270009815161^1024*3125^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        341 3125 2851270009815161 50000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (341/3125 : ℝ)) (X := (2851270009815161/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4517/1024 : ℝ) ≤ (6670518346813249/25000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4517 ≤ (6670518346813249/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4517*25000000000000000000^1024 ≤ 6670518346813249^1024*50000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 6670518346813249 25000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (6670518346813249/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002851270009815161/25000000000000000000 : ℝ) ≤ (10000258540778959/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (25002851270009815161/25000000000000000000 : ℝ)^1024 ≤ (10000258540778959/10000000000000000 : ℝ)^4517 := by
      have hnat : (25002851270009815161 : ℕ)^1024*10000000000000000^4517 ≤ 10000258540778959^4517*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002851270009815161 25000000000000000000 10000258540778959 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000258540778959/10000000000000000 : ℝ)) (X := (25002851270009815161/25000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016192306703441659/50000000000000000000 : ℝ) ≤ (200014681289597/200000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50016192306703441659/50000000000000000000 : ℝ)^1024 ≤ (200014681289597/200000000000000 : ℝ)^4517 := by
      have hnat : (50016192306703441659 : ℕ)^1024*200000000000000^4517 ≤ 200014681289597^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016192306703441659 50000000000000000000 200014681289597 200000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200014681289597/200000000000000 : ℝ)) (X := (50016192306703441659/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506670518346813249/12500000000000000000 : ℝ) ≤ (10001209588180741/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (12506670518346813249/12500000000000000000 : ℝ)^1024 ≤ (10001209588180741/10000000000000000 : ℝ)^4517 := by
      have hnat : (12506670518346813249 : ℕ)^1024*10000000000000000^4517 ≤ 10001209588180741^4517*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506670518346813249 12500000000000000000 10001209588180741 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001209588180741/10000000000000000 : ℝ)) (X := (12506670518346813249/12500000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2851270009815161/50000000000000000000 : ℝ) ≤ ((22845401851055798723/22850000000000000000 : ℝ)+2*(475523700891/457000000000000 : ℝ)*(341/3125 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (22845401851055798723/22850000000000000000 : ℝ)+2*(475523700891/457000000000000 : ℝ)*(341/3125 : ℝ)=(10000258540778959/10000000000000000 : ℝ) by norm_num, show 1+2*(2851270009815161/50000000000000000000 : ℝ)=(25002851270009815161/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6670518346813249/25000000000000000000 : ℝ)+(2851270009815161/50000000000000000000 : ℝ) ≤ ((22845401851055798723/22850000000000000000 : ℝ)+(475523700891/457000000000000 : ℝ)*((7741/50000 : ℝ)+(341/3125 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (22845401851055798723/22850000000000000000 : ℝ)+(475523700891/457000000000000 : ℝ)*((7741/50000 : ℝ)+(341/3125 : ℝ))=(200014681289597/200000000000000 : ℝ) by norm_num, show 1+(6670518346813249/25000000000000000000 : ℝ)+(2851270009815161/50000000000000000000 : ℝ)=(50016192306703441659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6670518346813249/25000000000000000000 : ℝ) ≤ ((22845401851055798723/22850000000000000000 : ℝ)+2*(475523700891/457000000000000 : ℝ)*(7741/50000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (22845401851055798723/22850000000000000000 : ℝ)+2*(475523700891/457000000000000 : ℝ)*(7741/50000 : ℝ)=(10001209588180741/10000000000000000 : ℝ) by norm_num, show 1+2*(6670518346813249/25000000000000000000 : ℝ)=(12506670518346813249/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22845401851055798723/22850000000000000000 : ℝ)*(X 1 0+X 2 0)+(475523700891/457000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (341/3125 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22845401851055798723/22850000000000000000 : ℝ)) (alpha := (475523700891/457000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22845401851055798723/22850000000000000000 : ℝ)*(X 0 1+X 2 1)+(475523700891/457000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (341/3125 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22845401851055798723/22850000000000000000 : ℝ)) (alpha := (475523700891/457000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22845401851055798723/22850000000000000000 : ℝ)*(X 0 2+X 1 2)+(475523700891/457000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (341/3125 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22845401851055798723/22850000000000000000 : ℝ)) (alpha := (475523700891/457000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1655686573/10000000000 : ℝ)*X 0 0+(1080588429/2000000000 : ℝ)*X 0 1+(1080588397/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((658845447/1250000000 : ℝ)*X 1 0+(-57469761/312500000 : ℝ)*X 1 1+(33768389/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270763259/10000000000 : ℝ)*X 2 0+(5402942387/10000000000 : ℝ)*X 2 1+(-919516291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4473349659/10000000000 : ℝ)*X 0 0+(2087835551/5000000000 : ℝ)*X 0 1+(4175670599/10000000000 : ℝ)*X 0 2+(4473349659/10000000000 : ℝ)*X 1 0+(2087835551/5000000000 : ℝ)*X 1 1+(4175670599/10000000000 : ℝ)*X 1 2+(4473349659/10000000000 : ℝ)*X 2 0+(2087835551/5000000000 : ℝ)*X 2 1+(4175670599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1044372523/5000000000 : ℝ)*X 0 0+(5243591357/10000000000 : ℝ)*X 0 1+(2621795941/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2690857821/5000000000 : ℝ)*X 1 0+(-952372983/5000000000 : ℝ)*X 1 1+(655448939/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381715601/10000000000 : ℝ)*X 2 0+(131089793/250000000 : ℝ)*X 2 1+(-1904745741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2032355987/5000000000 : ℝ)*X 0 0+(2189927479/5000000000 : ℝ)*X 0 1+(437985557/1000000000 : ℝ)*X 0 2+(2032355987/5000000000 : ℝ)*X 1 0+(2189927479/5000000000 : ℝ)*X 1 1+(437985557/1000000000 : ℝ)*X 1 2+(2032355987/5000000000 : ℝ)*X 2 0+(2189927479/5000000000 : ℝ)*X 2 1+(437985557/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1997234611/10000000000 : ℝ)*X 0 0+(10023369/19531250 : ℝ)*X 0 1+(271169933/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628257123/5000000000 : ℝ)*X 1 0+(-1830350201/10000000000 : ℝ)*X 1 1+(2711699279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314128609/2500000000 : ℝ)*X 2 0+(5423398177/10000000000 : ℝ)*X 2 1+(-1830350467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((180986267/400000000 : ℝ)*X 0 0+(1037356547/2500000000 : ℝ)*X 0 1+(829885337/2000000000 : ℝ)*X 0 2+(180986267/400000000 : ℝ)*X 1 0+(1037356547/2500000000 : ℝ)*X 1 1+(829885337/2000000000 : ℝ)*X 1 2+(180986267/400000000 : ℝ)*X 2 0+(1037356547/2500000000 : ℝ)*X 2 1+(829885337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1747152109/10000000000 : ℝ)*X 0 0+(5510977003/10000000000 : ℝ)*X 0 1+(2614282831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392177353/10000000000 : ℝ)*X 1 0+(-119422717/625000000 : ℝ)*X 1 1+(26142829/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392177359/10000000000 : ℝ)*X 2 0+(1045713141/2000000000 : ℝ)*X 2 1+(-1910763591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4025318347/10000000000 : ℝ)*X 0 0+(175963471/400000000 : ℝ)*X 0 1+(17183927/39062500 : ℝ)*X 0 2+(4025318347/10000000000 : ℝ)*X 1 0+(175963471/400000000 : ℝ)*X 1 1+(17183927/39062500 : ℝ)*X 1 2+(4025318347/10000000000 : ℝ)*X 2 0+(175963471/400000000 : ℝ)*X 2 1+(17183927/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31869/50000 : ℝ) ≤ (-364089097178513476478990410908003/571250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2335319/1562500000000 : ℝ)*(lower3) + (374841/2500000000000 : ℝ)*(lower4) + (247827/5000000000000 : ℝ)*(upper5) + (2221893276742787/100000000000000 : ℝ)*(major0) + (2221893276742787/100000000000000 : ℝ)*(major1) + (2221893276742787/100000000000000 : ℝ)*(major2) + (155220163034833/5000000000000 : ℝ)*(sp4) + (1552190117571677/50000000000000 : ℝ)*(sp5) + (776095600209253/25000000000000 : ℝ)*(sp6) + (680301140709783/50000000000000 : ℝ)*(sp7) + (540978657/20000000000000 : ℝ)*(sp12) + (100509557/390625000000 : ℝ)*(sp13) + (11782376467/50000000000000 : ℝ)*(sp14) + (586906509/2500000000000 : ℝ)*(sp15) + (54425030307197/4000000000000 : ℝ)*(f.failure) + (1552202982794973/50000000000000 : ℝ)*(f.sum) + (88782246126933/22850000000000000000000000000 : ℝ)*base66 + (9517380534919911001/2285000000000000000000000000000000 : ℝ)*base67 + (6666456808224911001/2285000000000000000000000000000000 : ℝ)*base69 + (2403392362594911001/2285000000000000000000000000000000 : ℝ)*base71 + (117319064120783/22850000000000000000000000000 : ℝ)*base74 + (7970115440694911001/2285000000000000000000000000000000 : ℝ)*base75 + (1686006498495088999/2285000000000000000000000000000000 : ℝ)*base78 + (6491179923944911001/2285000000000000000000000000000000 : ℝ)*base79 + (140712282060683/22850000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1741307/400000000000000000000 : ℝ)*base90 + (1741307/400000000000000000000 : ℝ)*base92 + (1741307/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58623/100000 : ℝ) ≤ (16744877330019752093350149887343/28562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50586557/100000000000000 : ℝ)*(lower0) + (5290361/50000000000000 : ℝ)*(upper1) + (10007269/12500000000000 : ℝ)*(upper2) + (91398493/100000000000000 : ℝ)*(upper3) + (1600549/50000000000000 : ℝ)*(lower5) + (114903514810353/5000000000000 : ℝ)*(major0) + (114903514810353/5000000000000 : ℝ)*(major1) + (114903514810353/5000000000000 : ℝ)*(major2) + (792331086459513/25000000000000 : ℝ)*(sp0) + (792331086459513/25000000000000 : ℝ)*(sp1) + (1584661253180449/50000000000000 : ℝ)*(sp2) + (140726164513587/10000000000000 : ℝ)*(sp3) + (919738577/50000000000000 : ℝ)*(sp6) + (1600551283/12500000000000 : ℝ)*(sp11) + (703637224773067/50000000000000 : ℝ)*(f.failure) + (792331086459513/25000000000000 : ℝ)*(f.sum) + (25940589491/142812500000000000000000000 : ℝ)*base65 + (158237068435270781/114250000000000000000000000000000 : ℝ)*base68 + (1340600652303229219/114250000000000000000000000000000 : ℝ)*base69 + (855508828942229219/114250000000000000000000000000000 : ℝ)*base71 + (4789910176833/1142500000000000000000000000 : ℝ)*base73 + (1547541304848229219/114250000000000000000000000000000 : ℝ)*base75 + (779974476920229219/114250000000000000000000000000000 : ℝ)*base77 + (953227277124229219/114250000000000000000000000000000 : ℝ)*base79 + (2449913480673/1142500000000000000000000000 : ℝ)*base81 + (9294723/5000000000000000000000 : ℝ)*base89 + (9294723/5000000000000000000000 : ℝ)*base91 + (9294723/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20077/25000 : ℝ) ≤ (229388241877340296697865151192569/285625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4565589/6250000000000 : ℝ)*(upper0) + (8397429/25000000000000 : ℝ)*(upper2) + (14144287/50000000000000 : ℝ)*(lower5) + (1246045189019399/50000000000000 : ℝ)*(major0) + (1246045189019399/50000000000000 : ℝ)*(major1) + (1246045189019399/50000000000000 : ℝ)*(major2) + (69325970011/100000000000000 : ℝ)*(sp1) + (5806159907/25000000000000 : ℝ)*(sp3) + (114161187/4000000000000 : ℝ)*(sp4) + (42891427153459/1250000000000 : ℝ)*(sp8) + (3431254141623097/100000000000000 : ℝ)*(sp9) + (857830866898277/25000000000000 : ℝ)*(sp10) + (190757967070653/12500000000000 : ℝ)*(sp11) + (805160839/12500000000000 : ℝ)*(sp12) + (381521740301213/25000000000000 : ℝ)*(f.failure) + (857830866898277/25000000000000 : ℝ)*(f.sum) + (10336356044059/11425000000000000000000000000 : ℝ)*base65 + (7926133965254377477/1142500000000000000000000000000000 : ℝ)*base67 + (6726873346206877477/1142500000000000000000000000000000 : ℝ)*base69 + (4592752188686877477/1142500000000000000000000000000000 : ℝ)*base71 + (41122736259533/5712500000000000000000000000 : ℝ)*base74 + (1265629807446877477/1142500000000000000000000000000000 : ℝ)*base75 + (10778420974361877477/1142500000000000000000000000000000 : ℝ)*base77 + (689555470158122523/1142500000000000000000000000000000 : ℝ)*base80 + (2797767423709/11425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2834597/2500000000000000000000 : ℝ)*base89 + (2834597/2500000000000000000000 : ℝ)*base91 + (2834597/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17199/20000 : ℝ) ≤ (-61404353019382629253417778340393/71406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46316221/25000000000000 : ℝ)*(lower0) + (20415141/25000000000000 : ℝ)*(upper3) + (1304451/100000000000000 : ℝ)*(lower4) + (158195703388949/6250000000000 : ℝ)*(major0) + (158195703388949/6250000000000 : ℝ)*(major1) + (158195703388949/6250000000000 : ℝ)*(major2) + (272049379/10000000000000 : ℝ)*(sp0) + (834347613/1562500000000 : ℝ)*(sp5) + (56675669179/100000000000000 : ℝ)*(sp6) + (328156613/4000000000000 : ℝ)*(sp7) + (885232400095577/25000000000000 : ℝ)*(sp12) + (1770439461314433/50000000000000 : ℝ)*(sp13) + (3540875645206919/100000000000000 : ℝ)*(sp14) + (30999726119961/2000000000000 : ℝ)*(sp15) + (12399956079307/800000000000 : ℝ)*(f.failure) + (1770466160438049/50000000000000 : ℝ)*(f.sum) + (23983647032089/5712500000000000000000000000 : ℝ)*base66 + (1164721770455087127/142812500000000000000000000000000 : ℝ)*base67 + (1130008290094462127/142812500000000000000000000000000 : ℝ)*base69 + (566160740962587127/142812500000000000000000000000000 : ℝ)*base71 + (19979371135707/2856250000000000000000000000 : ℝ)*base74 + (1037294909511337127/142812500000000000000000000000000 : ℝ)*base75 + (718365468116962127/142812500000000000000000000000000 : ℝ)*base77 + (568069953718524627/142812500000000000000000000000000 : ℝ)*base79 + (8040094283311/5712500000000000000000000000 : ℝ)*base81 + (142717/80000000000000000000 : ℝ)*base90 + (142717/80000000000000000000 : ℝ)*base92 + (142717/80000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1511_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (341/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31869/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58623/100000 : ℝ) else (20077/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17199/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1511_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1511_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31869/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58623/100000 : ℝ) else (20077/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17199/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1511_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1511_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31869/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58623/100000 : ℝ) else (20077/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17199/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1511_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

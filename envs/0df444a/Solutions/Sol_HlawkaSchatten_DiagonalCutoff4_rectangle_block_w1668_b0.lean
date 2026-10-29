-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1668_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:39.973004+00:00
-- url     : https://prove2.me/submissions/51ec602d-8fed-4f16-9613-94373f2f792d

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
theorem support_rectangle_w1668_s0_0 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-730794071/5000000000 : ℝ)*x 0 + (2881719227/5000000000 : ℝ)*x 1 + (4933515847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730794071/5000000000 : ℝ)^4991 ≤ (4448480132491/50000000000000 : ℝ)^3967 := by
    have hnat : (730794071 : ℕ)^4991*50000000000000^3967 ≤ 4448480132491^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730794071 5000000000 4448480132491 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2881719227/5000000000 : ℝ)^4991 ≤ (49992691610561/100000000000000 : ℝ)^3967 := by
    have hnat : (2881719227 : ℕ)^4991*100000000000000^3967 ≤ 49992691610561^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881719227 5000000000 49992691610561 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4933515847/10000000000 : ℝ)^4991 ≤ (41110348109401/100000000000000 : ℝ)^3967 := by
    have hnat : (4933515847 : ℕ)^4991*100000000000000^3967 ≤ 41110348109401^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933515847 10000000000 41110348109401 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-730794071/5000000000 : ℝ), (2881719227/5000000000 : ℝ), (4933515847/10000000000 : ℝ)] ![(4448480132491/50000000000000 : ℝ), (49992691610561/100000000000000 : ℝ), (41110348109401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-730794071/5000000000 : ℝ)|^4991 ≤ (4448480132491/50000000000000 : ℝ)^3967
        have hw : |(-730794071/5000000000 : ℝ)|=(730794071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2881719227/5000000000 : ℝ)|^4991 ≤ (49992691610561/100000000000000 : ℝ)^3967
        have hw : |(2881719227/5000000000 : ℝ)|=(2881719227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4933515847/10000000000 : ℝ)|^4991 ≤ (41110348109401/100000000000000 : ℝ)^3967
        have hw : |(4933515847/10000000000 : ℝ)|=(4933515847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_1 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5430466733/10000000000 : ℝ)*x 0 + (-1915514873/10000000000 : ℝ)*x 1 + (4933516777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5430466733/10000000000 : ℝ)^4991 ≤ (46386412672697/100000000000000 : ℝ)^3967 := by
    have hnat : (5430466733 : ℕ)^4991*100000000000000^3967 ≤ 46386412672697^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430466733 10000000000 46386412672697 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915514873/10000000000 : ℝ)^4991 ≤ (12503229453741/100000000000000 : ℝ)^3967 := by
    have hnat : (1915514873 : ℕ)^4991*100000000000000^3967 ≤ 12503229453741^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915514873 10000000000 12503229453741 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4933516777/10000000000 : ℝ)^4991 ≤ (10277589464841/25000000000000 : ℝ)^3967 := by
    have hnat : (4933516777 : ℕ)^4991*25000000000000^3967 ≤ 10277589464841^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933516777 10000000000 10277589464841 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5430466733/10000000000 : ℝ), (-1915514873/10000000000 : ℝ), (4933516777/10000000000 : ℝ)] ![(46386412672697/100000000000000 : ℝ), (12503229453741/100000000000000 : ℝ), (10277589464841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5430466733/10000000000 : ℝ)|^4991 ≤ (46386412672697/100000000000000 : ℝ)^3967
        have hw : |(5430466733/10000000000 : ℝ)|=(5430466733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1915514873/10000000000 : ℝ)|^4991 ≤ (12503229453741/100000000000000 : ℝ)^3967
        have hw : |(-1915514873/10000000000 : ℝ)|=(1915514873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4933516777/10000000000 : ℝ)|^4991 ≤ (10277589464841/25000000000000 : ℝ)^3967
        have hw : |(4933516777/10000000000 : ℝ)|=(4933516777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_2 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2715234421/5000000000 : ℝ)*x 0 + (493351547/1000000000 : ℝ)*x 1 + (-957756891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2715234421/5000000000 : ℝ)^4991 ≤ (46386435337691/100000000000000 : ℝ)^3967 := by
    have hnat : (2715234421 : ℕ)^4991*100000000000000^3967 ≤ 46386435337691^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715234421 5000000000 46386435337691 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493351547/1000000000 : ℝ)^4991 ≤ (41110344156997/100000000000000 : ℝ)^3967 := by
    have hnat : (493351547 : ℕ)^4991*100000000000000^3967 ≤ 41110344156997^3967*1000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493351547 1000000000 41110344156997 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957756891/5000000000 : ℝ)^4991 ≤ (12503220494179/100000000000000 : ℝ)^3967 := by
    have hnat : (957756891 : ℕ)^4991*100000000000000^3967 ≤ 12503220494179^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957756891 5000000000 12503220494179 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2715234421/5000000000 : ℝ), (493351547/1000000000 : ℝ), (-957756891/5000000000 : ℝ)] ![(46386435337691/100000000000000 : ℝ), (41110344156997/100000000000000 : ℝ), (12503220494179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2715234421/5000000000 : ℝ)|^4991 ≤ (46386435337691/100000000000000 : ℝ)^3967
        have hw : |(2715234421/5000000000 : ℝ)|=(2715234421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493351547/1000000000 : ℝ)|^4991 ≤ (41110344156997/100000000000000 : ℝ)^3967
        have hw : |(493351547/1000000000 : ℝ)|=(493351547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957756891/5000000000 : ℝ)|^4991 ≤ (12503220494179/100000000000000 : ℝ)^3967
        have hw : |(-957756891/5000000000 : ℝ)|=(957756891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_3 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4082269883/10000000000 : ℝ)*x 0 + (617476221/2000000000 : ℝ)*x 1 + (5283365567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4082269883/10000000000 : ℝ)^4991 ≤ (3239395241291/10000000000000 : ℝ)^3967 := by
    have hnat : (4082269883 : ℕ)^4991*10000000000000^3967 ≤ 3239395241291^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082269883 10000000000 3239395241291 10000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617476221/2000000000 : ℝ)^4991 ≤ (5698734182133/25000000000000 : ℝ)^3967 := by
    have hnat : (617476221 : ℕ)^4991*25000000000000^3967 ≤ 5698734182133^3967*2000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617476221 2000000000 5698734182133 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5283365567/10000000000 : ℝ)^4991 ≤ (44811110840407/100000000000000 : ℝ)^3967 := by
    have hnat : (5283365567 : ℕ)^4991*100000000000000^3967 ≤ 44811110840407^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283365567 10000000000 44811110840407 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4082269883/10000000000 : ℝ), (617476221/2000000000 : ℝ), (5283365567/10000000000 : ℝ)] ![(3239395241291/10000000000000 : ℝ), (5698734182133/25000000000000 : ℝ), (44811110840407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4082269883/10000000000 : ℝ)|^4991 ≤ (3239395241291/10000000000000 : ℝ)^3967
        have hw : |(4082269883/10000000000 : ℝ)|=(4082269883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(617476221/2000000000 : ℝ)|^4991 ≤ (5698734182133/25000000000000 : ℝ)^3967
        have hw : |(617476221/2000000000 : ℝ)|=(617476221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5283365567/10000000000 : ℝ)|^4991 ≤ (44811110840407/100000000000000 : ℝ)^3967
        have hw : |(5283365567/10000000000 : ℝ)|=(5283365567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_4 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91480637/625000000 : ℝ)*x 0 + (495390059/1000000000 : ℝ)*x 1 + (5742359833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91480637/625000000 : ℝ)^4991 ≤ (8913061738769/100000000000000 : ℝ)^3967 := by
    have hnat : (91480637 : ℕ)^4991*100000000000000^3967 ≤ 8913061738769^3967*625000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91480637 625000000 8913061738769 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495390059/1000000000 : ℝ)^4991 ≤ (2582760759617/6250000000000 : ℝ)^3967 := by
    have hnat : (495390059 : ℕ)^4991*6250000000000^3967 ≤ 2582760759617^3967*1000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495390059 1000000000 2582760759617 6250000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5742359833/10000000000 : ℝ)^4991 ≤ (995255321667/2000000000000 : ℝ)^3967 := by
    have hnat : (5742359833 : ℕ)^4991*2000000000000^3967 ≤ 995255321667^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5742359833 10000000000 995255321667 2000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91480637/625000000 : ℝ), (495390059/1000000000 : ℝ), (5742359833/10000000000 : ℝ)] ![(8913061738769/100000000000000 : ℝ), (2582760759617/6250000000000 : ℝ), (995255321667/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91480637/625000000 : ℝ)|^4991 ≤ (8913061738769/100000000000000 : ℝ)^3967
        have hw : |(-91480637/625000000 : ℝ)|=(91480637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(495390059/1000000000 : ℝ)|^4991 ≤ (2582760759617/6250000000000 : ℝ)^3967
        have hw : |(495390059/1000000000 : ℝ)|=(495390059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5742359833/10000000000 : ℝ)|^4991 ≤ (995255321667/2000000000000 : ℝ)^3967
        have hw : |(5742359833/10000000000 : ℝ)|=(5742359833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_5 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204149693/10000000000 : ℝ)*x 0 + (-44266833/400000000 : ℝ)*x 1 + (5742361507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204149693/10000000000 : ℝ)^4991 ≤ (43967449274799/100000000000000 : ℝ)^3967 := by
    have hnat : (5204149693 : ℕ)^4991*100000000000000^3967 ≤ 43967449274799^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204149693 10000000000 43967449274799 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44266833/400000000 : ℝ)^4991 ≤ (3134883186447/50000000000000 : ℝ)^3967 := by
    have hnat : (44266833 : ℕ)^4991*50000000000000^3967 ≤ 3134883186447^3967*400000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44266833 400000000 3134883186447 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5742361507/10000000000 : ℝ)^4991 ≤ (49762784334699/100000000000000 : ℝ)^3967 := by
    have hnat : (5742361507 : ℕ)^4991*100000000000000^3967 ≤ 49762784334699^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5742361507 10000000000 49762784334699 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204149693/10000000000 : ℝ), (-44266833/400000000 : ℝ), (5742361507/10000000000 : ℝ)] ![(43967449274799/100000000000000 : ℝ), (3134883186447/50000000000000 : ℝ), (49762784334699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204149693/10000000000 : ℝ)|^4991 ≤ (43967449274799/100000000000000 : ℝ)^3967
        have hw : |(5204149693/10000000000 : ℝ)|=(5204149693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44266833/400000000 : ℝ)|^4991 ≤ (3134883186447/50000000000000 : ℝ)^3967
        have hw : |(-44266833/400000000 : ℝ)|=(44266833/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5742361507/10000000000 : ℝ)|^4991 ≤ (49762784334699/100000000000000 : ℝ)^3967
        have hw : |(5742361507/10000000000 : ℝ)|=(5742361507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_6 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602075019/5000000000 : ℝ)*x 0 + (2871180499/5000000000 : ℝ)*x 1 + (-69166943/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602075019/5000000000 : ℝ)^4991 ≤ (21983726470963/50000000000000 : ℝ)^3967 := by
    have hnat : (2602075019 : ℕ)^4991*50000000000000^3967 ≤ 21983726470963^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602075019 5000000000 21983726470963 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2871180499/5000000000 : ℝ)^4991 ≤ (9952555757031/20000000000000 : ℝ)^3967 := by
    have hnat : (2871180499 : ℕ)^4991*20000000000000^3967 ≤ 9952555757031^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2871180499 5000000000 9952555757031 20000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69166943/625000000 : ℝ)^4991 ≤ (6269768247517/100000000000000 : ℝ)^3967 := by
    have hnat : (69166943 : ℕ)^4991*100000000000000^3967 ≤ 6269768247517^3967*625000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69166943 625000000 6269768247517 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602075019/5000000000 : ℝ), (2871180499/5000000000 : ℝ), (-69166943/625000000 : ℝ)] ![(21983726470963/50000000000000 : ℝ), (9952555757031/20000000000000 : ℝ), (6269768247517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602075019/5000000000 : ℝ)|^4991 ≤ (21983726470963/50000000000000 : ℝ)^3967
        have hw : |(2602075019/5000000000 : ℝ)|=(2602075019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2871180499/5000000000 : ℝ)|^4991 ≤ (9952555757031/20000000000000 : ℝ)^3967
        have hw : |(2871180499/5000000000 : ℝ)|=(2871180499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69166943/625000000 : ℝ)|^4991 ≤ (6269768247517/100000000000000 : ℝ)^3967
        have hw : |(-69166943/625000000 : ℝ)|=(69166943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s0_7 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4087831313/10000000000 : ℝ)*x 0 + (1045885399/2000000000 : ℝ)*x 1 + (1571576819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4087831313/10000000000 : ℝ)^4991 ≤ (2028092832437/6250000000000 : ℝ)^3967 := by
    have hnat : (4087831313 : ℕ)^4991*6250000000000^3967 ≤ 2028092832437^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4087831313 10000000000 2028092832437 6250000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045885399/2000000000 : ℝ)^4991 ≤ (1105907472253/2500000000000 : ℝ)^3967 := by
    have hnat : (1045885399 : ℕ)^4991*2500000000000^3967 ≤ 1105907472253^3967*2000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045885399 2000000000 1105907472253 2500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1571576819/5000000000 : ℝ)^4991 ≤ (11657107885177/50000000000000 : ℝ)^3967 := by
    have hnat : (1571576819 : ℕ)^4991*50000000000000^3967 ≤ 11657107885177^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571576819 5000000000 11657107885177 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4087831313/10000000000 : ℝ), (1045885399/2000000000 : ℝ), (1571576819/5000000000 : ℝ)] ![(2028092832437/6250000000000 : ℝ), (1105907472253/2500000000000 : ℝ), (11657107885177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4087831313/10000000000 : ℝ)|^4991 ≤ (2028092832437/6250000000000 : ℝ)^3967
        have hw : |(4087831313/10000000000 : ℝ)|=(4087831313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045885399/2000000000 : ℝ)|^4991 ≤ (1105907472253/2500000000000 : ℝ)^3967
        have hw : |(1045885399/2000000000 : ℝ)|=(1045885399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1571576819/5000000000 : ℝ)|^4991 ≤ (11657107885177/50000000000000 : ℝ)^3967
        have hw : |(1571576819/5000000000 : ℝ)|=(1571576819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1668_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5183/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22981/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4987/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4987 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4987*1^1024 ≤ 0^1024*1^4987 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4987 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4987/1024 : ℝ) ≤ (230682962351982239/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4987 ≤ (230682962351982239/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4987*20000000000000000000^1024 ≤ 230682962351982239^1024*5^4987 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 230682962351982239 20000000000000000000 4987 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (230682962351982239/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4987 := by
      have hnat : (1 : ℕ)^1024*1^4987 ≤ 1^4987*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20230682962351982239/20000000000000000000 : ℝ) ≤ (2004715143256043/2000000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (20230682962351982239/20000000000000000000 : ℝ)^1024 ≤ (2004715143256043/2000000000000000 : ℝ)^4987 := by
      have hnat : (20230682962351982239 : ℕ)^1024*2000000000000000^4987 ≤ 2004715143256043^4987*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20230682962351982239 20000000000000000000 2004715143256043 2000000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004715143256043/2000000000000000 : ℝ)) (X := (20230682962351982239/20000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10230682962351982239/10000000000000000000 : ℝ) ≤ (1004715143256043/1000000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (10230682962351982239/10000000000000000000 : ℝ)^1024 ≤ (1004715143256043/1000000000000000 : ℝ)^4987 := by
      have hnat : (10230682962351982239 : ℕ)^1024*1000000000000000^4987 ≤ 1004715143256043^4987*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10230682962351982239 10000000000000000000 1004715143256043 1000000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004715143256043/1000000000000000 : ℝ)) (X := (10230682962351982239/10000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4715143256043/800000000000000 : ℝ)*(0 : ℝ))^(4987/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4715143256043/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(230682962351982239/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4715143256043/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4987/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4715143256043/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2004715143256043/2000000000000000 : ℝ) by norm_num, show 1+(230682962351982239/20000000000000000000 : ℝ)+(0 : ℝ)=(20230682962351982239/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(230682962351982239/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4715143256043/800000000000000 : ℝ)*(2/5 : ℝ))^(4987/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4715143256043/800000000000000 : ℝ)*(2/5 : ℝ)=(1004715143256043/1000000000000000 : ℝ) by norm_num, show 1+2*(230682962351982239/20000000000000000000 : ℝ)=(10230682962351982239/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4715143256043/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4715143256043/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4715143256043/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4715143256043/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4715143256043/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4715143256043/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-730794071/5000000000 : ℝ)*X 0 0+(2881719227/5000000000 : ℝ)*X 0 1+(4933515847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5430466733/10000000000 : ℝ)*X 1 0+(-1915514873/10000000000 : ℝ)*X 1 1+(4933516777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2715234421/5000000000 : ℝ)*X 2 0+(493351547/1000000000 : ℝ)*X 2 1+(-957756891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4082269883/10000000000 : ℝ)*X 0 0+(617476221/2000000000 : ℝ)*X 0 1+(5283365567/10000000000 : ℝ)*X 0 2+(4082269883/10000000000 : ℝ)*X 1 0+(617476221/2000000000 : ℝ)*X 1 1+(5283365567/10000000000 : ℝ)*X 1 2+(4082269883/10000000000 : ℝ)*X 2 0+(617476221/2000000000 : ℝ)*X 2 1+(5283365567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-91480637/625000000 : ℝ)*X 0 0+(495390059/1000000000 : ℝ)*X 0 1+(5742359833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5204149693/10000000000 : ℝ)*X 1 0+(-44266833/400000000 : ℝ)*X 1 1+(5742361507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2602075019/5000000000 : ℝ)*X 2 0+(2871180499/5000000000 : ℝ)*X 2 1+(-69166943/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4087831313/10000000000 : ℝ)*X 0 0+(1045885399/2000000000 : ℝ)*X 0 1+(1571576819/5000000000 : ℝ)*X 0 2+(4087831313/10000000000 : ℝ)*X 1 0+(1045885399/2000000000 : ℝ)*X 1 1+(1571576819/5000000000 : ℝ)*X 1 2+(4087831313/10000000000 : ℝ)*X 2 0+(1045885399/2000000000 : ℝ)*X 2 1+(1571576819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39112788703044423842229/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173089149/100000000000000 : ℝ)*(base1) + (1731811883/100000000000000 : ℝ)*(base19) + (2182272097/100000000000000 : ℝ)*(base23) + (4374527/25000000000000 : ℝ)*(base24) + (221421127/50000000000000 : ℝ)*(upper5) + (415083130621099/50000000000000 : ℝ)*(major0) + (415083130621099/50000000000000 : ℝ)*(major1) + (415083130621099/50000000000000 : ℝ)*(major2) + (301234415477177/25000000000000 : ℝ)*(sp0) + (1204946934515579/100000000000000 : ℝ)*(sp1) + (602473233278629/50000000000000 : ℝ)*(sp2) + (113845116294187/25000000000000 : ℝ)*(sp3) + (174648561/1562500000000 : ℝ)*(sp4) + (2891951123/100000000000000 : ℝ)*(sp7) + (455383530217021/100000000000000 : ℝ)*(f.failure) + (602474333163731/50000000000000 : ℝ)*(f.sum) + (48404237471257/20000000000000000000000000000 : ℝ)*base65 + (3526466371257/40000000000000000000000000000 : ℝ)*base67 + (79304283131257/40000000000000000000000000000 : ℝ)*base69 + (245538639451257/40000000000000000000000000000 : ℝ)*base71 + (1163665891257/20000000000000000000000000000 : ℝ)*base73 + (110926156131257/40000000000000000000000000000 : ℝ)*base75 + (111609766291257/40000000000000000000000000000 : ℝ)*base77 + (32627952348743/40000000000000000000000000000 : ℝ)*base80 + (163880938371257/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (16152191/5000000000000000000000 : ℝ)*base90 + (16152191/5000000000000000000000 : ℝ)*base92 + (16152191/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (274016792770911274919229/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (521507827/50000000000000 : ℝ)*(base19) + (229330307/20000000000000 : ℝ)*(base23) + (136144127/100000000000000 : ℝ)*(base32) + (65009517/20000000000000 : ℝ)*(upper3) + (66639897/50000000000000 : ℝ)*(upper5) + (873809294291967/100000000000000 : ℝ)*(major0) + (873809294291967/100000000000000 : ℝ)*(major1) + (873809294291967/100000000000000 : ℝ)*(major2) + (1024125179/25000000000000 : ℝ)*(sp1) + (454616793/10000000000000 : ℝ)*(sp2) + (79268416474283/6250000000000 : ℝ)*(sp4) + (634144762036079/50000000000000 : ℝ)*(sp5) + (634144485384531/50000000000000 : ℝ)*(sp6) + (239661780251973/50000000000000 : ℝ)*(sp7) + (479323696648073/100000000000000 : ℝ)*(f.failure) + (79268416474283/6250000000000 : ℝ)*(f.sum) + (41167069773419/40000000000000000000000000000 : ℝ)*base66 + (450133624093419/80000000000000000000000000000 : ℝ)*base68 + (3509430653419/80000000000000000000000000000 : ℝ)*base70 + (149352474493419/80000000000000000000000000000 : ℝ)*base72 + (331100634973419/40000000000000000000000000000 : ℝ)*base74 + (113183480226581/80000000000000000000000000000 : ℝ)*base75 + (478892877986581/80000000000000000000000000000 : ℝ)*base77 + (734643219426581/80000000000000000000000000000 : ℝ)*base79 + (248367914173419/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (36358717/5000000000000000000000 : ℝ)*base89 + (36358717/5000000000000000000000 : ℝ)*base91 + (36358717/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1668_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5183/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1668_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1668_s1_0 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-780119993/5000000000 : ℝ)*x 0 + (1096680783/2000000000 : ℝ)*x 1 + (2574639773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (780119993/5000000000 : ℝ)^4991 ≤ (4829478678401/50000000000000 : ℝ)^3967 := by
    have hnat : (780119993 : ℕ)^4991*50000000000000^3967 ≤ 4829478678401^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780119993 5000000000 4829478678401 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096680783/2000000000 : ℝ)^4991 ≤ (23478015904477/50000000000000 : ℝ)^3967 := by
    have hnat : (1096680783 : ℕ)^4991*50000000000000^3967 ≤ 23478015904477^3967*2000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096680783 2000000000 23478015904477 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574639773/5000000000 : ℝ)^4991 ≤ (43385010816193/100000000000000 : ℝ)^3967 := by
    have hnat : (2574639773 : ℕ)^4991*100000000000000^3967 ≤ 43385010816193^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574639773 5000000000 43385010816193 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-780119993/5000000000 : ℝ), (1096680783/2000000000 : ℝ), (2574639773/5000000000 : ℝ)] ![(4829478678401/50000000000000 : ℝ), (23478015904477/50000000000000 : ℝ), (43385010816193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-780119993/5000000000 : ℝ)|^4991 ≤ (4829478678401/50000000000000 : ℝ)^3967
        have hw : |(-780119993/5000000000 : ℝ)|=(780119993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096680783/2000000000 : ℝ)|^4991 ≤ (23478015904477/50000000000000 : ℝ)^3967
        have hw : |(1096680783/2000000000 : ℝ)|=(1096680783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574639773/5000000000 : ℝ)|^4991 ≤ (43385010816193/100000000000000 : ℝ)^3967
        have hw : |(2574639773/5000000000 : ℝ)|=(2574639773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_1 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677985381/5000000000 : ℝ)*x 0 + (-216695119/1250000000 : ℝ)*x 1 + (5149279553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677985381/5000000000 : ℝ)^4991 ≤ (11396810498013/25000000000000 : ℝ)^3967 := by
    have hnat : (2677985381 : ℕ)^4991*25000000000000^3967 ≤ 11396810498013^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677985381 5000000000 11396810498013 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216695119/1250000000 : ℝ)^4991 ≤ (1378468388437/12500000000000 : ℝ)^3967 := by
    have hnat : (216695119 : ℕ)^4991*12500000000000^3967 ≤ 1378468388437^3967*1250000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216695119 1250000000 1378468388437 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149279553/10000000000 : ℝ)^4991 ≤ (8677002178079/20000000000000 : ℝ)^3967 := by
    have hnat : (5149279553 : ℕ)^4991*20000000000000^3967 ≤ 8677002178079^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149279553 10000000000 8677002178079 20000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677985381/5000000000 : ℝ), (-216695119/1250000000 : ℝ), (5149279553/10000000000 : ℝ)] ![(11396810498013/25000000000000 : ℝ), (1378468388437/12500000000000 : ℝ), (8677002178079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677985381/5000000000 : ℝ)|^4991 ≤ (11396810498013/25000000000000 : ℝ)^3967
        have hw : |(2677985381/5000000000 : ℝ)|=(2677985381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216695119/1250000000 : ℝ)|^4991 ≤ (1378468388437/12500000000000 : ℝ)^3967
        have hw : |(-216695119/1250000000 : ℝ)|=(216695119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149279553/10000000000 : ℝ)|^4991 ≤ (8677002178079/20000000000000 : ℝ)^3967
        have hw : |(5149279553/10000000000 : ℝ)|=(5149279553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_2 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338992663/2500000000 : ℝ)*x 0 + (64365997/125000000 : ℝ)*x 1 + (-216695103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338992663/2500000000 : ℝ)^4991 ≤ (1424601275441/3125000000000 : ℝ)^3967 := by
    have hnat : (1338992663 : ℕ)^4991*3125000000000^3967 ≤ 1424601275441^3967*2500000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338992663 2500000000 1424601275441 3125000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64365997/125000000 : ℝ)^4991 ≤ (2169250654233/5000000000000 : ℝ)^3967 := by
    have hnat : (64365997 : ℕ)^4991*5000000000000^3967 ≤ 2169250654233^3967*125000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64365997 125000000 2169250654233 5000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216695103/1250000000 : ℝ)^4991 ≤ (1378468260383/12500000000000 : ℝ)^3967 := by
    have hnat : (216695103 : ℕ)^4991*12500000000000^3967 ≤ 1378468260383^3967*1250000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216695103 1250000000 1378468260383 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338992663/2500000000 : ℝ), (64365997/125000000 : ℝ), (-216695103/1250000000 : ℝ)] ![(1424601275441/3125000000000 : ℝ), (2169250654233/5000000000000 : ℝ), (1378468260383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338992663/2500000000 : ℝ)|^4991 ≤ (1424601275441/3125000000000 : ℝ)^3967
        have hw : |(1338992663/2500000000 : ℝ)|=(1338992663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64365997/125000000 : ℝ)|^4991 ≤ (2169250654233/5000000000000 : ℝ)^3967
        have hw : |(64365997/125000000 : ℝ)|=(64365997/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216695103/1250000000 : ℝ)|^4991 ≤ (1378468260383/12500000000000 : ℝ)^3967
        have hw : |(-216695103/1250000000 : ℝ)|=(216695103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_3 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2080506811/5000000000 : ℝ)*x 0 + (1867762463/5000000000 : ℝ)*x 1 + (4619621011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080506811/5000000000 : ℝ)^4991 ≤ (8295511768011/25000000000000 : ℝ)^3967 := by
    have hnat : (2080506811 : ℕ)^4991*25000000000000^3967 ≤ 8295511768011^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080506811 5000000000 8295511768011 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867762463/5000000000 : ℝ)^4991 ≤ (28970964335957/100000000000000 : ℝ)^3967 := by
    have hnat : (1867762463 : ℕ)^4991*100000000000000^3967 ≤ 28970964335957^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867762463 5000000000 28970964335957 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4619621011/10000000000 : ℝ)^4991 ≤ (18923494288471/50000000000000 : ℝ)^3967 := by
    have hnat : (4619621011 : ℕ)^4991*50000000000000^3967 ≤ 18923494288471^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619621011 10000000000 18923494288471 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2080506811/5000000000 : ℝ), (1867762463/5000000000 : ℝ), (4619621011/10000000000 : ℝ)] ![(8295511768011/25000000000000 : ℝ), (28970964335957/100000000000000 : ℝ), (18923494288471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2080506811/5000000000 : ℝ)|^4991 ≤ (8295511768011/25000000000000 : ℝ)^3967
        have hw : |(2080506811/5000000000 : ℝ)|=(2080506811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1867762463/5000000000 : ℝ)|^4991 ≤ (28970964335957/100000000000000 : ℝ)^3967
        have hw : |(1867762463/5000000000 : ℝ)|=(1867762463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4619621011/10000000000 : ℝ)|^4991 ≤ (18923494288471/50000000000000 : ℝ)^3967
        have hw : |(4619621011/10000000000 : ℝ)|=(4619621011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_4 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-48761737/312500000 : ℝ)*x 0 + (5152579351/10000000000 : ℝ)*x 1 + (5480058667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48761737/312500000 : ℝ)^4991 ≤ (4830006749469/50000000000000 : ℝ)^3967 := by
    have hnat : (48761737 : ℕ)^4991*50000000000000^3967 ≤ 4830006749469^3967*312500000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48761737 312500000 4830006749469 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152579351/10000000000 : ℝ)^4991 ≤ (5427499083531/12500000000000 : ℝ)^3967 := by
    have hnat : (5152579351 : ℕ)^4991*12500000000000^3967 ≤ 5427499083531^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152579351 10000000000 5427499083531 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480058667/10000000000 : ℝ)^4991 ≤ (4691999381257/10000000000000 : ℝ)^3967 := by
    have hnat : (5480058667 : ℕ)^4991*10000000000000^3967 ≤ 4691999381257^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480058667 10000000000 4691999381257 10000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48761737/312500000 : ℝ), (5152579351/10000000000 : ℝ), (5480058667/10000000000 : ℝ)] ![(4830006749469/50000000000000 : ℝ), (5427499083531/12500000000000 : ℝ), (4691999381257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48761737/312500000 : ℝ)|^4991 ≤ (4830006749469/50000000000000 : ℝ)^3967
        have hw : |(-48761737/312500000 : ℝ)|=(48761737/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152579351/10000000000 : ℝ)|^4991 ≤ (5427499083531/12500000000000 : ℝ)^3967
        have hw : |(5152579351/10000000000 : ℝ)|=(5152579351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480058667/10000000000 : ℝ)|^4991 ≤ (4691999381257/10000000000000 : ℝ)^3967
        have hw : |(5480058667/10000000000 : ℝ)|=(5480058667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_5 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82288823/156250000 : ℝ)*x 0 + (-1402781689/10000000000 : ℝ)*x 1 + (1096011731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82288823/156250000 : ℝ)^4991 ≤ (44631051101759/100000000000000 : ℝ)^3967 := by
    have hnat : (82288823 : ℕ)^4991*100000000000000^3967 ≤ 44631051101759^3967*156250000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82288823 156250000 44631051101759 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402781689/10000000000 : ℝ)^4991 ≤ (8448955202379/100000000000000 : ℝ)^3967 := by
    have hnat : (1402781689 : ℕ)^4991*100000000000000^3967 ≤ 8448955202379^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402781689 10000000000 8448955202379 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096011731/2000000000 : ℝ)^4991 ≤ (9383998736661/20000000000000 : ℝ)^3967 := by
    have hnat : (1096011731 : ℕ)^4991*20000000000000^3967 ≤ 9383998736661^3967*2000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096011731 2000000000 9383998736661 20000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82288823/156250000 : ℝ), (-1402781689/10000000000 : ℝ), (1096011731/2000000000 : ℝ)] ![(44631051101759/100000000000000 : ℝ), (8448955202379/100000000000000 : ℝ), (9383998736661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82288823/156250000 : ℝ)|^4991 ≤ (44631051101759/100000000000000 : ℝ)^3967
        have hw : |(82288823/156250000 : ℝ)|=(82288823/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1402781689/10000000000 : ℝ)|^4991 ≤ (8448955202379/100000000000000 : ℝ)^3967
        have hw : |(-1402781689/10000000000 : ℝ)|=(1402781689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096011731/2000000000 : ℝ)|^4991 ≤ (9383998736661/20000000000000 : ℝ)^3967
        have hw : |(1096011731/2000000000 : ℝ)|=(1096011731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_6 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266484661/10000000000 : ℝ)*x 0 + (5480058667/10000000000 : ℝ)*x 1 + (-701390843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266484661/10000000000 : ℝ)^4991 ≤ (11157762746119/25000000000000 : ℝ)^3967 := by
    have hnat : (5266484661 : ℕ)^4991*25000000000000^3967 ≤ 11157762746119^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266484661 10000000000 11157762746119 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480058667/10000000000 : ℝ)^4991 ≤ (4691999381257/10000000000000 : ℝ)^3967 := by
    have hnat : (5480058667 : ℕ)^4991*10000000000000^3967 ≤ 4691999381257^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480058667 10000000000 4691999381257 10000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (701390843/5000000000 : ℝ)^4991 ≤ (4224477589823/50000000000000 : ℝ)^3967 := by
    have hnat : (701390843 : ℕ)^4991*50000000000000^3967 ≤ 4224477589823^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701390843 5000000000 4224477589823 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266484661/10000000000 : ℝ), (5480058667/10000000000 : ℝ), (-701390843/5000000000 : ℝ)] ![(11157762746119/25000000000000 : ℝ), (4691999381257/10000000000000 : ℝ), (4224477589823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266484661/10000000000 : ℝ)|^4991 ≤ (11157762746119/25000000000000 : ℝ)^3967
        have hw : |(5266484661/10000000000 : ℝ)|=(5266484661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480058667/10000000000 : ℝ)|^4991 ≤ (4691999381257/10000000000000 : ℝ)^3967
        have hw : |(5480058667/10000000000 : ℝ)|=(5480058667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-701390843/5000000000 : ℝ)|^4991 ≤ (4224477589823/50000000000000 : ℝ)^3967
        have hw : |(-701390843/5000000000 : ℝ)|=(701390843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s1_7 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416137107/1000000000 : ℝ)*x 0 + (2305444709/5000000000 : ℝ)*x 1 + (1872188083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416137107/1000000000 : ℝ)^4991 ≤ (2074102085999/6250000000000 : ℝ)^3967 := by
    have hnat : (416137107 : ℕ)^4991*6250000000000^3967 ≤ 2074102085999^3967*1000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416137107 1000000000 2074102085999 6250000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305444709/5000000000 : ℝ)^4991 ≤ (18878505133933/50000000000000 : ℝ)^3967 := by
    have hnat : (2305444709 : ℕ)^4991*50000000000000^3967 ≤ 18878505133933^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305444709 5000000000 18878505133933 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872188083/5000000000 : ℝ)^4991 ≤ (29057356333367/100000000000000 : ℝ)^3967 := by
    have hnat : (1872188083 : ℕ)^4991*100000000000000^3967 ≤ 29057356333367^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872188083 5000000000 29057356333367 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416137107/1000000000 : ℝ), (2305444709/5000000000 : ℝ), (1872188083/5000000000 : ℝ)] ![(2074102085999/6250000000000 : ℝ), (18878505133933/50000000000000 : ℝ), (29057356333367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416137107/1000000000 : ℝ)|^4991 ≤ (2074102085999/6250000000000 : ℝ)^3967
        have hw : |(416137107/1000000000 : ℝ)|=(416137107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2305444709/5000000000 : ℝ)|^4991 ≤ (18878505133933/50000000000000 : ℝ)^3967
        have hw : |(2305444709/5000000000 : ℝ)|=(2305444709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872188083/5000000000 : ℝ)|^4991 ≤ (29057356333367/100000000000000 : ℝ)^3967
        have hw : |(1872188083/5000000000 : ℝ)|=(1872188083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1668_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3419/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5183/100000 : ℝ) ^ (4987/1024 : ℝ) ≤ (5493635641899/10000000000000000000 : ℝ) := by
    have hpowers : (5183/100000 : ℝ)^4987 ≤ (5493635641899/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5183 : ℕ)^4987*10000000000000000000^1024 ≤ 5493635641899^1024*100000^4987 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5183 100000 5493635641899 10000000000000000000 4987 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5183/100000 : ℝ)) (X := (5493635641899/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22981/100000 : ℝ) ^ (4987/1024 : ℝ) ≤ (77587509966717323/100000000000000000000 : ℝ) := by
    have hpowers : (22981/100000 : ℝ)^4987 ≤ (77587509966717323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22981 : ℕ)^4987*100000000000000000000^1024 ≤ 77587509966717323^1024*100000^4987 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22981 100000 77587509966717323 100000000000000000000 4987 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22981/100000 : ℝ)) (X := (77587509966717323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000005493635641899/5000000000000000000 : ℝ) ≤ (1250000282007241/1250000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (5000005493635641899/5000000000000000000 : ℝ)^1024 ≤ (1250000282007241/1250000000000000 : ℝ)^4987 := by
      have hnat : (5000005493635641899 : ℕ)^1024*1250000000000000^4987 ≤ 1250000282007241^4987*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000005493635641899 5000000000000000000 1250000282007241 1250000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000282007241/1250000000000000 : ℝ)) (X := (5000005493635641899/5000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077642446323136313/100000000000000000000 : ℝ) ≤ (5000796885391341/5000000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (100077642446323136313/100000000000000000000 : ℝ)^1024 ≤ (5000796885391341/5000000000000000 : ℝ)^4987 := by
      have hnat : (100077642446323136313 : ℕ)^1024*5000000000000000^4987 ≤ 5000796885391341^4987*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077642446323136313 100000000000000000000 5000796885391341 5000000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000796885391341/5000000000000000 : ℝ)) (X := (100077642446323136313/100000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50077587509966717323/50000000000000000000 : ℝ) ≤ (2500796321376859/2500000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (50077587509966717323/50000000000000000000 : ℝ)^1024 ≤ (2500796321376859/2500000000000000 : ℝ)^4987 := by
      have hnat : (50077587509966717323 : ℕ)^1024*2500000000000000^4987 ≤ 2500796321376859^4987*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077587509966717323 50000000000000000000 2500796321376859 2500000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500796321376859/2500000000000000 : ℝ)) (X := (50077587509966717323/50000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5493635641899/10000000000000000000 : ℝ) ≤ ((8898177125584110129/8899000000000000000 : ℝ)+2*(795757362377/889900000000000 : ℝ)*(5183/100000 : ℝ))^(4987/1024 : ℝ) := by
    rw [show (8898177125584110129/8899000000000000000 : ℝ)+2*(795757362377/889900000000000 : ℝ)*(5183/100000 : ℝ)=(1250000282007241/1250000000000000 : ℝ) by norm_num, show 1+2*(5493635641899/10000000000000000000 : ℝ)=(5000005493635641899/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77587509966717323/100000000000000000000 : ℝ)+(5493635641899/10000000000000000000 : ℝ) ≤ ((8898177125584110129/8899000000000000000 : ℝ)+(795757362377/889900000000000 : ℝ)*((22981/100000 : ℝ)+(5183/100000 : ℝ)))^(4987/1024 : ℝ) := by
    rw [show (8898177125584110129/8899000000000000000 : ℝ)+(795757362377/889900000000000 : ℝ)*((22981/100000 : ℝ)+(5183/100000 : ℝ))=(5000796885391341/5000000000000000 : ℝ) by norm_num, show 1+(77587509966717323/100000000000000000000 : ℝ)+(5493635641899/10000000000000000000 : ℝ)=(100077642446323136313/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77587509966717323/100000000000000000000 : ℝ) ≤ ((8898177125584110129/8899000000000000000 : ℝ)+2*(795757362377/889900000000000 : ℝ)*(22981/100000 : ℝ))^(4987/1024 : ℝ) := by
    rw [show (8898177125584110129/8899000000000000000 : ℝ)+2*(795757362377/889900000000000 : ℝ)*(22981/100000 : ℝ)=(2500796321376859/2500000000000000 : ℝ) by norm_num, show 1+2*(77587509966717323/100000000000000000000 : ℝ)=(50077587509966717323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8898177125584110129/8899000000000000000 : ℝ)*(X 1 0+X 2 0)+(795757362377/889900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (5183/100000 : ℝ)) (hi := (22981/100000 : ℝ)) (c := (8898177125584110129/8899000000000000000 : ℝ)) (alpha := (795757362377/889900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8898177125584110129/8899000000000000000 : ℝ)*(X 0 1+X 2 1)+(795757362377/889900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (5183/100000 : ℝ)) (hi := (22981/100000 : ℝ)) (c := (8898177125584110129/8899000000000000000 : ℝ)) (alpha := (795757362377/889900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8898177125584110129/8899000000000000000 : ℝ)*(X 0 2+X 1 2)+(795757362377/889900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (5183/100000 : ℝ)) (hi := (22981/100000 : ℝ)) (c := (8898177125584110129/8899000000000000000 : ℝ)) (alpha := (795757362377/889900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-780119993/5000000000 : ℝ)*X 0 0+(1096680783/2000000000 : ℝ)*X 0 1+(2574639773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677985381/5000000000 : ℝ)*X 1 0+(-216695119/1250000000 : ℝ)*X 1 1+(5149279553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338992663/2500000000 : ℝ)*X 2 0+(64365997/125000000 : ℝ)*X 2 1+(-216695103/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2080506811/5000000000 : ℝ)*X 0 0+(1867762463/5000000000 : ℝ)*X 0 1+(4619621011/10000000000 : ℝ)*X 0 2+(2080506811/5000000000 : ℝ)*X 1 0+(1867762463/5000000000 : ℝ)*X 1 1+(4619621011/10000000000 : ℝ)*X 1 2+(2080506811/5000000000 : ℝ)*X 2 0+(1867762463/5000000000 : ℝ)*X 2 1+(4619621011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-48761737/312500000 : ℝ)*X 0 0+(5152579351/10000000000 : ℝ)*X 0 1+(5480058667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82288823/156250000 : ℝ)*X 1 0+(-1402781689/10000000000 : ℝ)*X 1 1+(1096011731/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266484661/10000000000 : ℝ)*X 2 0+(5480058667/10000000000 : ℝ)*X 2 1+(-701390843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((416137107/1000000000 : ℝ)*X 0 0+(2305444709/5000000000 : ℝ)*X 0 1+(1872188083/5000000000 : ℝ)*X 0 2+(416137107/1000000000 : ℝ)*X 1 0+(2305444709/5000000000 : ℝ)*X 1 1+(1872188083/5000000000 : ℝ)*X 1 2+(416137107/1000000000 : ℝ)*X 2 0+(2305444709/5000000000 : ℝ)*X 2 1+(1872188083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1536450736472753362283265873/222475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (942768423/100000000000000 : ℝ)*(base19) + (66037667/12500000000000 : ℝ)*(base23) + (189065307/100000000000000 : ℝ)*(lower2) + (214542253/100000000000000 : ℝ)*(upper3) + (624099/20000000000000 : ℝ)*(upper5) + (1031004934126979/50000000000000 : ℝ)*(major0) + (1031004934126979/50000000000000 : ℝ)*(major1) + (1031004934126979/50000000000000 : ℝ)*(major2) + (748226738509371/25000000000000 : ℝ)*(sp0) + (2992913413894477/100000000000000 : ℝ)*(sp1) + (748228457090391/25000000000000 : ℝ)*(sp2) + (141387614365933/12500000000000 : ℝ)*(sp3) + (925328177/12500000000000 : ℝ)*(sp4) + (4234711797/100000000000000 : ℝ)*(sp7) + (1131105149639261/100000000000000 : ℝ)*(f.failure) + (29929143566629/1000000000000 : ℝ)*(f.sum) + (46433910612671/11123750000000000000000000000 : ℝ)*base66 + (991806323038799709/444950000000000000000000000000000 : ℝ)*base68 + (1938682228664000291/444950000000000000000000000000000 : ℝ)*base69 + (2468506561300500291/444950000000000000000000000000000 : ℝ)*base71 + (241338627471/43452148437500000000000000 : ℝ)*base74 + (1857607164058749709/444950000000000000000000000000000 : ℝ)*base76 + (1386334784816799709/444950000000000000000000000000000 : ℝ)*base78 + (535914897530599709/444950000000000000000000000000000 : ℝ)*base80 + (42802386565379/11123750000000000000000000000 : ℝ)*base81 + (7540769/5000000000000000000000 : ℝ)*base89 + (7540769/5000000000000000000000 : ℝ)*base91 + (7540769/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3654715079738048562365932353/444950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259356919/20000000000000 : ℝ)*(base19) + (138857817/10000000000000 : ℝ)*(base23) + (23680583/12500000000000 : ℝ)*(upper3) + (43640973/100000000000000 : ℝ)*(lower4) + (92833977/50000000000000 : ℝ)*(upper5) + (2103838980974981/100000000000000 : ℝ)*(major0) + (2103838980974981/100000000000000 : ℝ)*(major1) + (2103838980974981/100000000000000 : ℝ)*(major2) + (742621759/6250000000000 : ℝ)*(sp1) + (12782768333/100000000000000 : ℝ)*(sp2) + (3053627388967079/100000000000000 : ℝ)*(sp4) + (3053614210234339/100000000000000 : ℝ)*(sp5) + (95425413050643/3125000000000 : ℝ)*(sp6) + (28851257479767/2500000000000 : ℝ)*(sp7) + (28851257479767/2500000000000 : ℝ)*(f.failure) + (3053627388967079/100000000000000 : ℝ)*(f.sum) + (257326792184157/44495000000000000000000000000 : ℝ)*base65 + (8000511644817047451/889900000000000000000000000000000 : ℝ)*base68 + (1397324822283352549/889900000000000000000000000000000 : ℝ)*base69 + (7671218990069652549/889900000000000000000000000000000 : ℝ)*base71 + (49016354250879/22247500000000000000000000000 : ℝ)*base74 + (5607415039521752549/889900000000000000000000000000000 : ℝ)*base75 + (3622858931861252549/889900000000000000000000000000000 : ℝ)*base77 + (915115869432747451/889900000000000000000000000000000 : ℝ)*base80 + (199441160402597/44495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1333357/125000000000000000000 : ℝ)*base90 + (1333357/125000000000000000000 : ℝ)*base92 + (1333357/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1668_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3419/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1668_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1668_s2_0 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97998373/625000000 : ℝ)*x 0 + (5444881277/10000000000 : ℝ)*x 1 + (1295670677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97998373/625000000 : ℝ)^4991 ≤ (1214904175921/12500000000000 : ℝ)^3967 := by
    have hnat : (97998373 : ℕ)^4991*12500000000000^3967 ≤ 1214904175921^3967*625000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97998373 625000000 1214904175921 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444881277/10000000000 : ℝ)^4991 ≤ (11635343967477/25000000000000 : ℝ)^3967 := by
    have hnat : (5444881277 : ℕ)^4991*25000000000000^3967 ≤ 11635343967477^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444881277 10000000000 11635343967477 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295670677/2500000000 : ℝ)^4991 ≤ (21869695351123/50000000000000 : ℝ)^3967 := by
    have hnat : (1295670677 : ℕ)^4991*50000000000000^3967 ≤ 21869695351123^3967*2500000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295670677 2500000000 21869695351123 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97998373/625000000 : ℝ), (5444881277/10000000000 : ℝ), (1295670677/2500000000 : ℝ)] ![(1214904175921/12500000000000 : ℝ), (11635343967477/25000000000000 : ℝ), (21869695351123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97998373/625000000 : ℝ)|^4991 ≤ (1214904175921/12500000000000 : ℝ)^3967
        have hw : |(-97998373/625000000 : ℝ)|=(97998373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444881277/10000000000 : ℝ)|^4991 ≤ (11635343967477/25000000000000 : ℝ)^3967
        have hw : |(5444881277/10000000000 : ℝ)|=(5444881277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295670677/2500000000 : ℝ)|^4991 ≤ (21869695351123/50000000000000 : ℝ)^3967
        have hw : |(1295670677/2500000000 : ℝ)|=(1295670677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_1 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672858283/5000000000 : ℝ)*x 0 + (-1702928477/10000000000 : ℝ)*x 1 + (2591341453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672858283/5000000000 : ℝ)^4991 ≤ (1421170675401/3125000000000 : ℝ)^3967 := by
    have hnat : (2672858283 : ℕ)^4991*3125000000000^3967 ≤ 1421170675401^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672858283 5000000000 1421170675401 3125000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1702928477/10000000000 : ℝ)^4991 ≤ (1347893196373/12500000000000 : ℝ)^3967 := by
    have hnat : (1702928477 : ℕ)^4991*12500000000000^3967 ≤ 1347893196373^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702928477 10000000000 1347893196373 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591341453/5000000000 : ℝ)^4991 ≤ (43739392804613/100000000000000 : ℝ)^3967 := by
    have hnat : (2591341453 : ℕ)^4991*100000000000000^3967 ≤ 43739392804613^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591341453 5000000000 43739392804613 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672858283/5000000000 : ℝ), (-1702928477/10000000000 : ℝ), (2591341453/5000000000 : ℝ)] ![(1421170675401/3125000000000 : ℝ), (1347893196373/12500000000000 : ℝ), (43739392804613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672858283/5000000000 : ℝ)|^4991 ≤ (1421170675401/3125000000000 : ℝ)^3967
        have hw : |(2672858283/5000000000 : ℝ)|=(2672858283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1702928477/10000000000 : ℝ)|^4991 ≤ (1347893196373/12500000000000 : ℝ)^3967
        have hw : |(-1702928477/10000000000 : ℝ)|=(1702928477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591341453/5000000000 : ℝ)|^4991 ≤ (43739392804613/100000000000000 : ℝ)^3967
        have hw : |(2591341453/5000000000 : ℝ)|=(2591341453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_2 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83526821/156250000 : ℝ)*x 0 + (2591341393/5000000000 : ℝ)*x 1 + (-851464333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83526821/156250000 : ℝ)^4991 ≤ (568468267217/1250000000000 : ℝ)^3967 := by
    have hnat : (83526821 : ℕ)^4991*1250000000000^3967 ≤ 568468267217^3967*156250000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83526821 156250000 568468267217 1250000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591341393/5000000000 : ℝ)^4991 ≤ (43739391530451/100000000000000 : ℝ)^3967 := by
    have hnat : (2591341393 : ℕ)^4991*100000000000000^3967 ≤ 43739391530451^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591341393 5000000000 43739391530451 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851464333/5000000000 : ℝ)^4991 ≤ (2695786769169/25000000000000 : ℝ)^3967 := by
    have hnat : (851464333 : ℕ)^4991*25000000000000^3967 ≤ 2695786769169^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851464333 5000000000 2695786769169 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83526821/156250000 : ℝ), (2591341393/5000000000 : ℝ), (-851464333/5000000000 : ℝ)] ![(568468267217/1250000000000 : ℝ), (43739391530451/100000000000000 : ℝ), (2695786769169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83526821/156250000 : ℝ)|^4991 ≤ (568468267217/1250000000000 : ℝ)^3967
        have hw : |(83526821/156250000 : ℝ)|=(83526821/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591341393/5000000000 : ℝ)|^4991 ≤ (43739391530451/100000000000000 : ℝ)^3967
        have hw : |(2591341393/5000000000 : ℝ)|=(2591341393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-851464333/5000000000 : ℝ)|^4991 ≤ (2695786769169/25000000000000 : ℝ)^3967
        have hw : |(-851464333/5000000000 : ℝ)|=(851464333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_3 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166802853/10000000000 : ℝ)*x 0 + (957528657/2500000000 : ℝ)*x 1 + (2261947027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166802853/10000000000 : ℝ)^4991 ≤ (33240140665021/100000000000000 : ℝ)^3967 := by
    have hnat : (4166802853 : ℕ)^4991*100000000000000^3967 ≤ 33240140665021^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166802853 10000000000 33240140665021 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957528657/2500000000 : ℝ)^4991 ≤ (14948458510979/50000000000000 : ℝ)^3967 := by
    have hnat : (957528657 : ℕ)^4991*50000000000000^3967 ≤ 14948458510979^3967*2500000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957528657 2500000000 14948458510979 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261947027/5000000000 : ℝ)^4991 ≤ (9215735574287/25000000000000 : ℝ)^3967 := by
    have hnat : (2261947027 : ℕ)^4991*25000000000000^3967 ≤ 9215735574287^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261947027 5000000000 9215735574287 25000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166802853/10000000000 : ℝ), (957528657/2500000000 : ℝ), (2261947027/5000000000 : ℝ)] ![(33240140665021/100000000000000 : ℝ), (14948458510979/50000000000000 : ℝ), (9215735574287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166802853/10000000000 : ℝ)|^4991 ≤ (33240140665021/100000000000000 : ℝ)^3967
        have hw : |(4166802853/10000000000 : ℝ)|=(4166802853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957528657/2500000000 : ℝ)|^4991 ≤ (14948458510979/50000000000000 : ℝ)^3967
        have hw : |(957528657/2500000000 : ℝ)|=(957528657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261947027/5000000000 : ℝ)|^4991 ≤ (9215735574287/25000000000000 : ℝ)^3967
        have hw : |(2261947027/5000000000 : ℝ)|=(2261947027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_4 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-784019663/5000000000 : ℝ)*x 0 + (207388799/400000000 : ℝ)*x 1 + (5442822201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784019663/5000000000 : ℝ)^4991 ≤ (1214967889153/12500000000000 : ℝ)^3967 := by
    have hnat : (784019663 : ℕ)^4991*12500000000000^3967 ≤ 1214967889153^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784019663 5000000000 1214967889153 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207388799/400000000 : ℝ)^4991 ≤ (5470127942283/12500000000000 : ℝ)^3967 := by
    have hnat : (207388799 : ℕ)^4991*12500000000000^3967 ≤ 5470127942283^3967*400000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207388799 400000000 5470127942283 12500000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442822201/10000000000 : ℝ)^4991 ≤ (9303846666881/20000000000000 : ℝ)^3967 := by
    have hnat : (5442822201 : ℕ)^4991*20000000000000^3967 ≤ 9303846666881^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442822201 10000000000 9303846666881 20000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784019663/5000000000 : ℝ), (207388799/400000000 : ℝ), (5442822201/10000000000 : ℝ)] ![(1214967889153/12500000000000 : ℝ), (5470127942283/12500000000000 : ℝ), (9303846666881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784019663/5000000000 : ℝ)|^4991 ≤ (1214967889153/12500000000000 : ℝ)^3967
        have hw : |(-784019663/5000000000 : ℝ)|=(784019663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207388799/400000000 : ℝ)|^4991 ≤ (5470127942283/12500000000000 : ℝ)^3967
        have hw : |(207388799/400000000 : ℝ)|=(207388799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442822201/10000000000 : ℝ)|^4991 ≤ (9303846666881/20000000000000 : ℝ)^3967
        have hw : |(5442822201/10000000000 : ℝ)|=(5442822201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_5 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637766081/5000000000 : ℝ)*x 0 + (-721394541/5000000000 : ℝ)*x 1 + (544282231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637766081/5000000000 : ℝ)^4991 ≤ (8945507496413/20000000000000 : ℝ)^3967 := by
    have hnat : (2637766081 : ℕ)^4991*20000000000000^3967 ≤ 8945507496413^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637766081 5000000000 8945507496413 20000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721394541/5000000000 : ℝ)^4991 ≤ (8753227993919/100000000000000 : ℝ)^3967 := by
    have hnat : (721394541 : ℕ)^4991*100000000000000^3967 ≤ 8753227993919^3967*5000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721394541 5000000000 8753227993919 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544282231/1000000000 : ℝ)^4991 ≤ (46519234506493/100000000000000 : ℝ)^3967 := by
    have hnat : (544282231 : ℕ)^4991*100000000000000^3967 ≤ 46519234506493^3967*1000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544282231 1000000000 46519234506493 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637766081/5000000000 : ℝ), (-721394541/5000000000 : ℝ), (544282231/1000000000 : ℝ)] ![(8945507496413/20000000000000 : ℝ), (8753227993919/100000000000000 : ℝ), (46519234506493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637766081/5000000000 : ℝ)|^4991 ≤ (8945507496413/20000000000000 : ℝ)^3967
        have hw : |(2637766081/5000000000 : ℝ)|=(2637766081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-721394541/5000000000 : ℝ)|^4991 ≤ (8753227993919/100000000000000 : ℝ)^3967
        have hw : |(-721394541/5000000000 : ℝ)|=(721394541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544282231/1000000000 : ℝ)|^4991 ≤ (46519234506493/100000000000000 : ℝ)^3967
        have hw : |(544282231/1000000000 : ℝ)|=(544282231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_6 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318883067/2500000000 : ℝ)*x 0 + (5442822147/10000000000 : ℝ)*x 1 + (-360697291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318883067/2500000000 : ℝ)^4991 ≤ (8945507722549/20000000000000 : ℝ)^3967 := by
    have hnat : (1318883067 : ℕ)^4991*20000000000000^3967 ≤ 8945507722549^3967*2500000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318883067 2500000000 8945507722549 20000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442822147/10000000000 : ℝ)^4991 ≤ (46519232753737/100000000000000 : ℝ)^3967 := by
    have hnat : (5442822147 : ℕ)^4991*100000000000000^3967 ≤ 46519232753737^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442822147 10000000000 46519232753737 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360697291/2500000000 : ℝ)^4991 ≤ (4376614309909/50000000000000 : ℝ)^3967 := by
    have hnat : (360697291 : ℕ)^4991*50000000000000^3967 ≤ 4376614309909^3967*2500000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360697291 2500000000 4376614309909 50000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318883067/2500000000 : ℝ), (5442822147/10000000000 : ℝ), (-360697291/2500000000 : ℝ)] ![(8945507722549/20000000000000 : ℝ), (46519232753737/100000000000000 : ℝ), (4376614309909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318883067/2500000000 : ℝ)|^4991 ≤ (8945507722549/20000000000000 : ℝ)^3967
        have hw : |(1318883067/2500000000 : ℝ)|=(1318883067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442822147/10000000000 : ℝ)|^4991 ≤ (46519232753737/100000000000000 : ℝ)^3967
        have hw : |(5442822147/10000000000 : ℝ)|=(5442822147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360697291/2500000000 : ℝ)|^4991 ≤ (4376614309909/50000000000000 : ℝ)^3967
        have hw : |(-360697291/2500000000 : ℝ)|=(360697291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1668_s2_7 (p : ℝ) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041744003/2500000000 : ℝ)*x 0 + (4518503839/10000000000 : ℝ)*x 1 + (3835562693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041744003/2500000000 : ℝ)^4991 ≤ (33241878596573/100000000000000 : ℝ)^3967 := by
    have hnat : (1041744003 : ℕ)^4991*100000000000000^3967 ≤ 33241878596573^3967*2500000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041744003 2500000000 33241878596573 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518503839/10000000000 : ℝ)^4991 ≤ (36807691033181/100000000000000 : ℝ)^3967 := by
    have hnat : (4518503839 : ℕ)^4991*100000000000000^3967 ≤ 36807691033181^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518503839 10000000000 36807691033181 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3835562693/10000000000 : ℝ)^4991 ≤ (29950430352213/100000000000000 : ℝ)^3967 := by
    have hnat : (3835562693 : ℕ)^4991*100000000000000^3967 ≤ 29950430352213^3967*10000000000^4991 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3835562693 10000000000 29950430352213 100000000000000 4991 3967 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4991/1024 : ℝ)) 4991 3967 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041744003/2500000000 : ℝ), (4518503839/10000000000 : ℝ), (3835562693/10000000000 : ℝ)] ![(33241878596573/100000000000000 : ℝ), (36807691033181/100000000000000 : ℝ), (29950430352213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041744003/2500000000 : ℝ)|^4991 ≤ (33241878596573/100000000000000 : ℝ)^3967
        have hw : |(1041744003/2500000000 : ℝ)|=(1041744003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518503839/10000000000 : ℝ)|^4991 ≤ (36807691033181/100000000000000 : ℝ)^3967
        have hw : |(4518503839/10000000000 : ℝ)|=(4518503839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3835562693/10000000000 : ℝ)|^4991 ≤ (29950430352213/100000000000000 : ℝ)^3967
        have hw : |(3835562693/10000000000 : ℝ)|=(3835562693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1668_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3419/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2677/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16289/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3419/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3419/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3419/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3419/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3419/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3419/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9987/100000 : ℝ) ^ (4987/1024 : ℝ) ≤ (670041100918531/50000000000000000000 : ℝ) := by
    have hpowers : (9987/100000 : ℝ)^4987 ≤ (670041100918531/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9987 : ℕ)^4987*50000000000000000000^1024 ≤ 670041100918531^1024*100000^4987 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9987 100000 670041100918531 50000000000000000000 4987 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9987/100000 : ℝ)) (X := (670041100918531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3419/20000 : ℝ) ^ (4987/1024 : ℝ) ≤ (18364649493490309/100000000000000000000 : ℝ) := by
    have hpowers : (3419/20000 : ℝ)^4987 ≤ (18364649493490309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3419 : ℕ)^4987*100000000000000000000^1024 ≤ 18364649493490309^1024*20000^4987 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3419 20000 18364649493490309 100000000000000000000 4987 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3419/20000 : ℝ)) (X := (18364649493490309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000670041100918531/25000000000000000000 : ℝ) ≤ (10000055032266359/10000000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (25000670041100918531/25000000000000000000 : ℝ)^1024 ≤ (10000055032266359/10000000000000000 : ℝ)^4987 := by
      have hnat : (25000670041100918531 : ℕ)^1024*10000000000000000^4987 ≤ 10000055032266359^4987*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000670041100918531 25000000000000000000 10000055032266359 10000000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055032266359/10000000000000000 : ℝ)) (X := (25000670041100918531/25000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019704731695327371/100000000000000000000 : ℝ) ≤ (10000404573203639/10000000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (100019704731695327371/100000000000000000000 : ℝ)^1024 ≤ (10000404573203639/10000000000000000 : ℝ)^4987 := by
      have hnat : (100019704731695327371 : ℕ)^1024*10000000000000000^4987 ≤ 10000404573203639^4987*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019704731695327371 100000000000000000000 10000404573203639 10000000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000404573203639/10000000000000000 : ℝ)) (X := (100019704731695327371/100000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018364649493490309/50000000000000000000 : ℝ) ≤ (10000754114140919/10000000000000000 : ℝ) ^ (4987/1024 : ℝ) := by
    have hpowers : (50018364649493490309/50000000000000000000 : ℝ)^1024 ≤ (10000754114140919/10000000000000000 : ℝ)^4987 := by
      have hnat : (50018364649493490309 : ℕ)^1024*10000000000000000^4987 ≤ 10000754114140919^4987*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018364649493490309 50000000000000000000 10000754114140919 10000000000000000 1024 4987 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754114140919/10000000000000000 : ℝ)) (X := (50018364649493490309/50000000000000000000 : ℝ)) (by norm_num) 4987 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(670041100918531/50000000000000000000 : ℝ) ≤ ((17768352359667012263/17770000000000000000 : ℝ)+2*(1092315429/2221250000000 : ℝ)*(9987/100000 : ℝ))^(4987/1024 : ℝ) := by
    rw [show (17768352359667012263/17770000000000000000 : ℝ)+2*(1092315429/2221250000000 : ℝ)*(9987/100000 : ℝ)=(10000055032266359/10000000000000000 : ℝ) by norm_num, show 1+2*(670041100918531/50000000000000000000 : ℝ)=(25000670041100918531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18364649493490309/100000000000000000000 : ℝ)+(670041100918531/50000000000000000000 : ℝ) ≤ ((17768352359667012263/17770000000000000000 : ℝ)+(1092315429/2221250000000 : ℝ)*((3419/20000 : ℝ)+(9987/100000 : ℝ)))^(4987/1024 : ℝ) := by
    rw [show (17768352359667012263/17770000000000000000 : ℝ)+(1092315429/2221250000000 : ℝ)*((3419/20000 : ℝ)+(9987/100000 : ℝ))=(10000404573203639/10000000000000000 : ℝ) by norm_num, show 1+(18364649493490309/100000000000000000000 : ℝ)+(670041100918531/50000000000000000000 : ℝ)=(100019704731695327371/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18364649493490309/100000000000000000000 : ℝ) ≤ ((17768352359667012263/17770000000000000000 : ℝ)+2*(1092315429/2221250000000 : ℝ)*(3419/20000 : ℝ))^(4987/1024 : ℝ) := by
    rw [show (17768352359667012263/17770000000000000000 : ℝ)+2*(1092315429/2221250000000 : ℝ)*(3419/20000 : ℝ)=(10000754114140919/10000000000000000 : ℝ) by norm_num, show 1+2*(18364649493490309/100000000000000000000 : ℝ)=(50018364649493490309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17768352359667012263/17770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1092315429/2221250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (9987/100000 : ℝ)) (hi := (3419/20000 : ℝ)) (c := (17768352359667012263/17770000000000000000 : ℝ)) (alpha := (1092315429/2221250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17768352359667012263/17770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1092315429/2221250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (9987/100000 : ℝ)) (hi := (3419/20000 : ℝ)) (c := (17768352359667012263/17770000000000000000 : ℝ)) (alpha := (1092315429/2221250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17768352359667012263/17770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1092315429/2221250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4987/1024 : ℝ)) (lo := (9987/100000 : ℝ)) (hi := (3419/20000 : ℝ)) (c := (17768352359667012263/17770000000000000000 : ℝ)) (alpha := (1092315429/2221250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-97998373/625000000 : ℝ)*X 0 0+(5444881277/10000000000 : ℝ)*X 0 1+(1295670677/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672858283/5000000000 : ℝ)*X 1 0+(-1702928477/10000000000 : ℝ)*X 1 1+(2591341453/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83526821/156250000 : ℝ)*X 2 0+(2591341393/5000000000 : ℝ)*X 2 1+(-851464333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166802853/10000000000 : ℝ)*X 0 0+(957528657/2500000000 : ℝ)*X 0 1+(2261947027/5000000000 : ℝ)*X 0 2+(4166802853/10000000000 : ℝ)*X 1 0+(957528657/2500000000 : ℝ)*X 1 1+(2261947027/5000000000 : ℝ)*X 1 2+(4166802853/10000000000 : ℝ)*X 2 0+(957528657/2500000000 : ℝ)*X 2 1+(2261947027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-784019663/5000000000 : ℝ)*X 0 0+(207388799/400000000 : ℝ)*X 0 1+(5442822201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2637766081/5000000000 : ℝ)*X 1 0+(-721394541/5000000000 : ℝ)*X 1 1+(544282231/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1318883067/2500000000 : ℝ)*X 2 0+(5442822147/10000000000 : ℝ)*X 2 1+(-360697291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1041744003/2500000000 : ℝ)*X 0 0+(4518503839/10000000000 : ℝ)*X 0 1+(3835562693/10000000000 : ℝ)*X 0 2+(1041744003/2500000000 : ℝ)*X 1 0+(4518503839/10000000000 : ℝ)*X 1 1+(3835562693/10000000000 : ℝ)*X 1 2+(1041744003/2500000000 : ℝ)*X 2 0+(4518503839/10000000000 : ℝ)*X 2 1+(3835562693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1668_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1094823292852379216049546609/88850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (964026611/50000000000000 : ℝ)*(base19) + (182888149/10000000000000 : ℝ)*(base23) + (446237/1000000000000 : ℝ)*(lower2) + (383756421/100000000000000 : ℝ)*(upper3) + (84492047/50000000000000 : ℝ)*(upper5) + (262767750359873/10000000000000 : ℝ)*(major0) + (262767750359873/10000000000000 : ℝ)*(major1) + (262767750359873/10000000000000 : ℝ)*(major2) + (3813931453419717/100000000000000 : ℝ)*(sp0) + (3813953380424451/100000000000000 : ℝ)*(sp1) + (3813953479596183/100000000000000 : ℝ)*(sp2) + (288277761505531/20000000000000 : ℝ)*(sp3) + (5963764489/25000000000000 : ℝ)*(sp4) + (10480453689/100000000000000 : ℝ)*(sp7) + (45043727749417/3125000000000 : ℝ)*(f.failure) + (3813955308477673/100000000000000 : ℝ)*(f.sum) + (8708136670153/1777000000000000000000000000 : ℝ)*base65 + (1046325053466122599/177700000000000000000000000000000 : ℝ)*base67 + (750496576139822599/177700000000000000000000000000000 : ℝ)*base69 + (1420933689742822599/177700000000000000000000000000000 : ℝ)*base71 + (650197271987/444250000000000000000000000 : ℝ)*base74 + (146050059192022599/177700000000000000000000000000000 : ℝ)*base75 + (2472882809720622599/177700000000000000000000000000000 : ℝ)*base77 + (1776033021342822599/177700000000000000000000000000000 : ℝ)*base79 + (9388125324193/1777000000000000000000000000 : ℝ)*base82 + (1458507/156250000000000000000 : ℝ)*base90 + (1458507/156250000000000000000 : ℝ)*base92 + (1458507/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4801062533555628644226143847/444250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194741599/12500000000000 : ℝ)*(base19) + (222841311/12500000000000 : ℝ)*(base23) + (249441491/100000000000000 : ℝ)*(upper3) + (34373783/50000000000000 : ℝ)*(lower4) + (210876961/100000000000000 : ℝ)*(upper5) + (2669343782800677/100000000000000 : ℝ)*(major0) + (2669343782800677/100000000000000 : ℝ)*(major1) + (2669343782800677/100000000000000 : ℝ)*(major2) + (9663424053/50000000000000 : ℝ)*(sp1) + (5144334317/25000000000000 : ℝ)*(sp2) + (154977283573591/4000000000000 : ℝ)*(sp4) + (968602801139719/25000000000000 : ℝ)*(sp5) + (3874409729272019/100000000000000 : ℝ)*(sp6) + (146425511602427/10000000000000 : ℝ)*(sp7) + (146425511602427/10000000000000 : ℝ)*(f.failure) + (154977283573591/4000000000000 : ℝ)*(f.sum) + (6972336257749/888500000000000000000000000 : ℝ)*base65 + (23363367285072702051/1777000000000000000000000000000000 : ℝ)*base67 + (10783227762862702051/1777000000000000000000000000000000 : ℝ)*base69 + (25996655618511702051/1777000000000000000000000000000000 : ℝ)*base71 + (1341382875407/222125000000000000000000000 : ℝ)*base73 + (16072193145945702051/1777000000000000000000000000000000 : ℝ)*base75 + (16704941232159702051/1777000000000000000000000000000000 : ℝ)*base77 + (1116527523959297949/1777000000000000000000000000000000 : ℝ)*base80 + (4376305481883/888500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6994217/500000000000000000000 : ℝ)*base90 + (6994217/500000000000000000000 : ℝ)*base92 + (6994217/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1668_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3419/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1668_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1668_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1668_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1668_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1668_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4987/1024 : ℝ) ≤ p) (hpb : p ≤ (4991/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (91150229/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1668_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

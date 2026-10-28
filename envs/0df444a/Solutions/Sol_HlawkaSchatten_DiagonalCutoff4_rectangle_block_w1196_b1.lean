-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:16.268652+00:00
-- url     : https://prove2.me/submissions/40bd2378-f413-4643-8b65-5214bf55bbe8

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
theorem support_rectangle_w1196_s3_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138074323/10000000000 : ℝ)*x 0 + (169495119/312500000 : ℝ)*x 1 + (209476293/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138074323/10000000000 : ℝ)^8389 ≤ (6495390639111/50000000000000 : ℝ)^6341 := by
    have hnat : (2138074323 : ℕ)^8389*50000000000000^6341 ≤ 6495390639111^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138074323 10000000000 6495390639111 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169495119/312500000 : ℝ)^8389 ≤ (11128442659497/25000000000000 : ℝ)^6341 := by
    have hnat : (169495119 : ℕ)^8389*25000000000000^6341 ≤ 11128442659497^6341*312500000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169495119 312500000 11128442659497 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209476293/400000000 : ℝ)^8389 ≤ (42495448069133/100000000000000 : ℝ)^6341 := by
    have hnat : (209476293 : ℕ)^8389*100000000000000^6341 ≤ 42495448069133^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209476293 400000000 42495448069133 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138074323/10000000000 : ℝ), (169495119/312500000 : ℝ), (209476293/400000000 : ℝ)] ![(6495390639111/50000000000000 : ℝ), (11128442659497/25000000000000 : ℝ), (42495448069133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138074323/10000000000 : ℝ)|^8389 ≤ (6495390639111/50000000000000 : ℝ)^6341
        have hw : |(-2138074323/10000000000 : ℝ)|=(2138074323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169495119/312500000 : ℝ)|^8389 ≤ (11128442659497/25000000000000 : ℝ)^6341
        have hw : |(169495119/312500000 : ℝ)|=(169495119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209476293/400000000 : ℝ)|^8389 ≤ (42495448069133/100000000000000 : ℝ)^6341
        have hw : |(209476293/400000000 : ℝ)|=(209476293/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352524717/10000000000 : ℝ)*x 0 + (-2233521643/10000000000 : ℝ)*x 1 + (40913341/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352524717/10000000000 : ℝ)^8389 ≤ (273381595863/625000000000 : ℝ)^6341 := by
    have hnat : (5352524717 : ℕ)^8389*625000000000^6341 ≤ 273381595863^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352524717 10000000000 273381595863 625000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233521643/10000000000 : ℝ)^8389 ≤ (3440873278141/25000000000000 : ℝ)^6341 := by
    have hnat : (2233521643 : ℕ)^8389*25000000000000^6341 ≤ 3440873278141^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233521643 10000000000 3440873278141 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40913341/78125000 : ℝ)^8389 ≤ (42495451536681/100000000000000 : ℝ)^6341 := by
    have hnat : (40913341 : ℕ)^8389*100000000000000^6341 ≤ 42495451536681^6341*78125000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40913341 78125000 42495451536681 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352524717/10000000000 : ℝ), (-2233521643/10000000000 : ℝ), (40913341/78125000 : ℝ)] ![(273381595863/625000000000 : ℝ), (3440873278141/25000000000000 : ℝ), (42495451536681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352524717/10000000000 : ℝ)|^8389 ≤ (273381595863/625000000000 : ℝ)^6341
        have hw : |(5352524717/10000000000 : ℝ)|=(5352524717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233521643/10000000000 : ℝ)|^8389 ≤ (3440873278141/25000000000000 : ℝ)^6341
        have hw : |(-2233521643/10000000000 : ℝ)|=(2233521643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40913341/78125000 : ℝ)|^8389 ≤ (42495451536681/100000000000000 : ℝ)^6341
        have hw : |(40913341/78125000 : ℝ)|=(40913341/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352524539/10000000000 : ℝ)*x 0 + (2618453989/5000000000 : ℝ)*x 1 + (-558380361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352524539/10000000000 : ℝ)^8389 ≤ (21870526706823/50000000000000 : ℝ)^6341 := by
    have hnat : (5352524539 : ℕ)^8389*50000000000000^6341 ≤ 21870526706823^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352524539 10000000000 21870526706823 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618453989/5000000000 : ℝ)^8389 ≤ (42495455079377/100000000000000 : ℝ)^6341 := by
    have hnat : (2618453989 : ℕ)^8389*100000000000000^6341 ≤ 42495455079377^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618453989 5000000000 42495455079377 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558380361/2500000000 : ℝ)^8389 ≤ (1720436436277/12500000000000 : ℝ)^6341 := by
    have hnat : (558380361 : ℕ)^8389*12500000000000^6341 ≤ 1720436436277^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558380361 2500000000 1720436436277 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352524539/10000000000 : ℝ), (2618453989/5000000000 : ℝ), (-558380361/2500000000 : ℝ)] ![(21870526706823/50000000000000 : ℝ), (42495455079377/100000000000000 : ℝ), (1720436436277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352524539/10000000000 : ℝ)|^8389 ≤ (21870526706823/50000000000000 : ℝ)^6341
        have hw : |(5352524539/10000000000 : ℝ)|=(5352524539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618453989/5000000000 : ℝ)|^8389 ≤ (42495455079377/100000000000000 : ℝ)^6341
        have hw : |(2618453989/5000000000 : ℝ)|=(2618453989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558380361/2500000000 : ℝ)|^8389 ≤ (1720436436277/12500000000000 : ℝ)^6341
        have hw : |(-558380361/2500000000 : ℝ)|=(558380361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088796129/2500000000 : ℝ)*x 0 + (834248051/2000000000 : ℝ)*x 1 + (1136771973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088796129/2500000000 : ℝ)^8389 ≤ (8324417007669/25000000000000 : ℝ)^6341 := by
    have hnat : (1088796129 : ℕ)^8389*25000000000000^6341 ≤ 8324417007669^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088796129 2500000000 8324417007669 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834248051/2000000000 : ℝ)^8389 ≤ (1572495583137/5000000000000 : ℝ)^6341 := by
    have hnat : (834248051 : ℕ)^8389*5000000000000^6341 ≤ 1572495583137^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834248051 2000000000 1572495583137 5000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136771973/2500000000 : ℝ)^8389 ≤ (17626210144609/50000000000000 : ℝ)^6341 := by
    have hnat : (1136771973 : ℕ)^8389*50000000000000^6341 ≤ 17626210144609^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136771973 2500000000 17626210144609 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088796129/2500000000 : ℝ), (834248051/2000000000 : ℝ), (1136771973/2500000000 : ℝ)] ![(8324417007669/25000000000000 : ℝ), (1572495583137/5000000000000 : ℝ), (17626210144609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088796129/2500000000 : ℝ)|^8389 ≤ (8324417007669/25000000000000 : ℝ)^6341
        have hw : |(1088796129/2500000000 : ℝ)|=(1088796129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834248051/2000000000 : ℝ)|^8389 ≤ (1572495583137/5000000000000 : ℝ)^6341
        have hw : |(834248051/2000000000 : ℝ)|=(834248051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136771973/2500000000 : ℝ)|^8389 ≤ (17626210144609/50000000000000 : ℝ)^6341
        have hw : |(1136771973/2500000000 : ℝ)|=(1136771973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427618043/2000000000 : ℝ)*x 0 + (5237607013/10000000000 : ℝ)*x 1 + (2711570103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427618043/2000000000 : ℝ)^8389 ≤ (6495454511623/50000000000000 : ℝ)^6341 := by
    have hnat : (427618043 : ℕ)^8389*50000000000000^6341 ≤ 6495454511623^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427618043 2000000000 6495454511623 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237607013/10000000000 : ℝ)^8389 ≤ (42502959691753/100000000000000 : ℝ)^6341 := by
    have hnat : (5237607013 : ℕ)^8389*100000000000000^6341 ≤ 42502959691753^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237607013 10000000000 42502959691753 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711570103/5000000000 : ℝ)^8389 ≤ (44506131266713/100000000000000 : ℝ)^6341 := by
    have hnat : (2711570103 : ℕ)^8389*100000000000000^6341 ≤ 44506131266713^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711570103 5000000000 44506131266713 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427618043/2000000000 : ℝ), (5237607013/10000000000 : ℝ), (2711570103/5000000000 : ℝ)] ![(6495454511623/50000000000000 : ℝ), (42502959691753/100000000000000 : ℝ), (44506131266713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427618043/2000000000 : ℝ)|^8389 ≤ (6495454511623/50000000000000 : ℝ)^6341
        have hw : |(-427618043/2000000000 : ℝ)|=(427618043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237607013/10000000000 : ℝ)|^8389 ≤ (42502959691753/100000000000000 : ℝ)^6341
        have hw : |(5237607013/10000000000 : ℝ)|=(5237607013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711570103/5000000000 : ℝ)|^8389 ≤ (44506131266713/100000000000000 : ℝ)^6341
        have hw : |(2711570103/5000000000 : ℝ)|=(2711570103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060996577/2000000000 : ℝ)*x 0 + (-2047288653/10000000000 : ℝ)*x 1 + (5423140131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060996577/2000000000 : ℝ)^8389 ≤ (43227799035507/100000000000000 : ℝ)^6341 := by
    have hnat : (1060996577 : ℕ)^8389*100000000000000^6341 ≤ 43227799035507^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060996577 2000000000 43227799035507 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047288653/10000000000 : ℝ)^8389 ≤ (3066517622019/25000000000000 : ℝ)^6341 := by
    have hnat : (2047288653 : ℕ)^8389*25000000000000^6341 ≤ 3066517622019^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047288653 10000000000 3066517622019 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423140131/10000000000 : ℝ)^8389 ≤ (44506130452417/100000000000000 : ℝ)^6341 := by
    have hnat : (5423140131 : ℕ)^8389*100000000000000^6341 ≤ 44506130452417^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423140131 10000000000 44506130452417 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060996577/2000000000 : ℝ), (-2047288653/10000000000 : ℝ), (5423140131/10000000000 : ℝ)] ![(43227799035507/100000000000000 : ℝ), (3066517622019/25000000000000 : ℝ), (44506130452417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060996577/2000000000 : ℝ)|^8389 ≤ (43227799035507/100000000000000 : ℝ)^6341
        have hw : |(1060996577/2000000000 : ℝ)|=(1060996577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047288653/10000000000 : ℝ)|^8389 ≤ (3066517622019/25000000000000 : ℝ)^6341
        have hw : |(-2047288653/10000000000 : ℝ)|=(2047288653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423140131/10000000000 : ℝ)|^8389 ≤ (44506130452417/100000000000000 : ℝ)^6341
        have hw : |(5423140131/10000000000 : ℝ)|=(5423140131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304982497/10000000000 : ℝ)*x 0 + (5423140549/10000000000 : ℝ)*x 1 + (-204728861/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304982497/10000000000 : ℝ)^8389 ≤ (5403474356593/12500000000000 : ℝ)^6341 := by
    have hnat : (5304982497 : ℕ)^8389*12500000000000^6341 ≤ 5403474356593^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304982497 10000000000 5403474356593 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423140549/10000000000 : ℝ)^8389 ≤ (11126533747691/25000000000000 : ℝ)^6341 := by
    have hnat : (5423140549 : ℕ)^8389*25000000000000^6341 ≤ 11126533747691^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423140549 10000000000 11126533747691 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204728861/1000000000 : ℝ)^8389 ≤ (12266070147239/100000000000000 : ℝ)^6341 := by
    have hnat : (204728861 : ℕ)^8389*100000000000000^6341 ≤ 12266070147239^6341*1000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204728861 1000000000 12266070147239 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304982497/10000000000 : ℝ), (5423140549/10000000000 : ℝ), (-204728861/1000000000 : ℝ)] ![(5403474356593/12500000000000 : ℝ), (11126533747691/25000000000000 : ℝ), (12266070147239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304982497/10000000000 : ℝ)|^8389 ≤ (5403474356593/12500000000000 : ℝ)^6341
        have hw : |(5304982497/10000000000 : ℝ)|=(5304982497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423140549/10000000000 : ℝ)|^8389 ≤ (11126533747691/25000000000000 : ℝ)^6341
        have hw : |(5423140549/10000000000 : ℝ)|=(5423140549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204728861/1000000000 : ℝ)|^8389 ≤ (12266070147239/100000000000000 : ℝ)^6341
        have hw : |(-204728861/1000000000 : ℝ)|=(204728861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s3_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34841733/80000000 : ℝ)*x 0 + (2272840431/5000000000 : ℝ)*x 1 + (2086327167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34841733/80000000 : ℝ)^8389 ≤ (8324498202243/25000000000000 : ℝ)^6341 := by
    have hnat : (34841733 : ℕ)^8389*25000000000000^6341 ≤ 8324498202243^6341*80000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34841733 80000000 8324498202243 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272840431/5000000000 : ℝ)^8389 ≤ (35237989513233/100000000000000 : ℝ)^6341 := by
    have hnat : (2272840431 : ℕ)^8389*100000000000000^6341 ≤ 35237989513233^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272840431 5000000000 35237989513233 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086327167/5000000000 : ℝ)^8389 ≤ (31464017670297/100000000000000 : ℝ)^6341 := by
    have hnat : (2086327167 : ℕ)^8389*100000000000000^6341 ≤ 31464017670297^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086327167 5000000000 31464017670297 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34841733/80000000 : ℝ), (2272840431/5000000000 : ℝ), (2086327167/5000000000 : ℝ)] ![(8324498202243/25000000000000 : ℝ), (35237989513233/100000000000000 : ℝ), (31464017670297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34841733/80000000 : ℝ)|^8389 ≤ (8324498202243/25000000000000 : ℝ)^6341
        have hw : |(34841733/80000000 : ℝ)|=(34841733/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2272840431/5000000000 : ℝ)|^8389 ≤ (35237989513233/100000000000000 : ℝ)^6341
        have hw : |(2272840431/5000000000 : ℝ)|=(2272840431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086327167/5000000000 : ℝ)|^8389 ≤ (31464017670297/100000000000000 : ℝ)^6341
        have hw : |(2086327167/5000000000 : ℝ)|=(2086327167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10789/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2949/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2327/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2327/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2327/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2327/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2327/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2327/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2327/25000 : ℝ) ^ (2097/512 : ℝ) ≤ (5980559716101367/100000000000000000000 : ℝ) := by
    have hpowers : (2327/25000 : ℝ)^2097 ≤ (5980559716101367/100000000000000000000 : ℝ)^512 := by
      have hnat : (2327 : ℕ)^2097*100000000000000000000^512 ≤ 5980559716101367^512*25000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2327 25000 5980559716101367 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2327/25000 : ℝ)) (X := (5980559716101367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16347/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (15011214257444057/25000000000000000000 : ℝ) := by
    have hpowers : (16347/100000 : ℝ)^2097 ≤ (15011214257444057/25000000000000000000 : ℝ)^512 := by
      have hnat : (16347 : ℕ)^2097*25000000000000000000^512 ≤ 15011214257444057^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16347 100000 15011214257444057 25000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16347/100000 : ℝ)) (X := (15011214257444057/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005980559716101367/50000000000000000000 : ℝ) ≤ (5000146013741961/5000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50005980559716101367/50000000000000000000 : ℝ)^512 ≤ (5000146013741961/5000000000000000 : ℝ)^2097 := by
      have hnat : (50005980559716101367 : ℕ)^512*5000000000000000^2097 ≤ 5000146013741961^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005980559716101367 50000000000000000000 5000146013741961 5000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000146013741961/5000000000000000 : ℝ)) (X := (50005980559716101367/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013205083349175519/20000000000000000000 : ℝ) ≤ (10001611663398967/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (20013205083349175519/20000000000000000000 : ℝ)^512 ≤ (10001611663398967/10000000000000000 : ℝ)^2097 := by
      have hnat : (20013205083349175519 : ℕ)^512*10000000000000000^2097 ≤ 10001611663398967^2097*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013205083349175519 20000000000000000000 10001611663398967 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001611663398967/10000000000000000 : ℝ)) (X := (20013205083349175519/20000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515011214257444057/12500000000000000000 : ℝ) ≤ (2500732824828503/2500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (12515011214257444057/12500000000000000000 : ℝ)^512 ≤ (2500732824828503/2500000000000000 : ℝ)^2097 := by
      have hnat : (12515011214257444057 : ℕ)^512*2500000000000000^2097 ≤ 2500732824828503^2097*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515011214257444057 12500000000000000000 2500732824828503 2500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500732824828503/2500000000000000 : ℝ)) (X := (12515011214257444057/12500000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5980559716101367/100000000000000000000 : ℝ) ≤ ((35183744619632424619/35195000000000000000 : ℝ)+2*(263927183009/140780000000000 : ℝ)*(2327/25000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (35183744619632424619/35195000000000000000 : ℝ)+2*(263927183009/140780000000000 : ℝ)*(2327/25000 : ℝ)=(5000146013741961/5000000000000000 : ℝ) by norm_num, show 1+2*(5980559716101367/100000000000000000000 : ℝ)=(50005980559716101367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15011214257444057/25000000000000000000 : ℝ)+(5980559716101367/100000000000000000000 : ℝ) ≤ ((35183744619632424619/35195000000000000000 : ℝ)+(263927183009/140780000000000 : ℝ)*((16347/100000 : ℝ)+(2327/25000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (35183744619632424619/35195000000000000000 : ℝ)+(263927183009/140780000000000 : ℝ)*((16347/100000 : ℝ)+(2327/25000 : ℝ))=(10001611663398967/10000000000000000 : ℝ) by norm_num, show 1+(15011214257444057/25000000000000000000 : ℝ)+(5980559716101367/100000000000000000000 : ℝ)=(20013205083349175519/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15011214257444057/25000000000000000000 : ℝ) ≤ ((35183744619632424619/35195000000000000000 : ℝ)+2*(263927183009/140780000000000 : ℝ)*(16347/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (35183744619632424619/35195000000000000000 : ℝ)+2*(263927183009/140780000000000 : ℝ)*(16347/100000 : ℝ)=(2500732824828503/2500000000000000 : ℝ) by norm_num, show 1+2*(15011214257444057/25000000000000000000 : ℝ)=(12515011214257444057/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35183744619632424619/35195000000000000000 : ℝ)*(X 1 0+X 2 0)+(263927183009/140780000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (2327/25000 : ℝ)) (hi := (16347/100000 : ℝ)) (c := (35183744619632424619/35195000000000000000 : ℝ)) (alpha := (263927183009/140780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35183744619632424619/35195000000000000000 : ℝ)*(X 0 1+X 2 1)+(263927183009/140780000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (2327/25000 : ℝ)) (hi := (16347/100000 : ℝ)) (c := (35183744619632424619/35195000000000000000 : ℝ)) (alpha := (263927183009/140780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35183744619632424619/35195000000000000000 : ℝ)*(X 0 2+X 1 2)+(263927183009/140780000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (2327/25000 : ℝ)) (hi := (16347/100000 : ℝ)) (c := (35183744619632424619/35195000000000000000 : ℝ)) (alpha := (263927183009/140780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138074323/10000000000 : ℝ)*X 0 0+(169495119/312500000 : ℝ)*X 0 1+(209476293/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352524717/10000000000 : ℝ)*X 1 0+(-2233521643/10000000000 : ℝ)*X 1 1+(40913341/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352524539/10000000000 : ℝ)*X 2 0+(2618453989/5000000000 : ℝ)*X 2 1+(-558380361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088796129/2500000000 : ℝ)*X 0 0+(834248051/2000000000 : ℝ)*X 0 1+(1136771973/2500000000 : ℝ)*X 0 2+(1088796129/2500000000 : ℝ)*X 1 0+(834248051/2000000000 : ℝ)*X 1 1+(1136771973/2500000000 : ℝ)*X 1 2+(1088796129/2500000000 : ℝ)*X 2 0+(834248051/2000000000 : ℝ)*X 2 1+(1136771973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427618043/2000000000 : ℝ)*X 0 0+(5237607013/10000000000 : ℝ)*X 0 1+(2711570103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060996577/2000000000 : ℝ)*X 1 0+(-2047288653/10000000000 : ℝ)*X 1 1+(5423140131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304982497/10000000000 : ℝ)*X 2 0+(5423140549/10000000000 : ℝ)*X 2 1+(-204728861/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34841733/80000000 : ℝ)*X 0 0+(2272840431/5000000000 : ℝ)*X 0 1+(2086327167/5000000000 : ℝ)*X 0 2+(34841733/80000000 : ℝ)*X 1 0+(2272840431/5000000000 : ℝ)*X 1 1+(2086327167/5000000000 : ℝ)*X 1 2+(34841733/80000000 : ℝ)*X 2 0+(2272840431/5000000000 : ℝ)*X 2 1+(2086327167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8403202751082340883857252791/879875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1312781117/100000000000000 : ℝ)*(base19) + (467532667/50000000000000 : ℝ)*(base23) + (106952541/100000000000000 : ℝ)*(lower2) + (55405467/50000000000000 : ℝ)*(upper3) + (145082917/100000000000000 : ℝ)*(upper5) + (2002541151066179/50000000000000 : ℝ)*(major0) + (2002541151066179/50000000000000 : ℝ)*(major1) + (2002541151066179/50000000000000 : ℝ)*(major2) + (2674722596454969/50000000000000 : ℝ)*(sp0) + (1337370195942047/25000000000000 : ℝ)*(sp1) + (534948116148397/10000000000000 : ℝ)*(sp2) + (665166877876099/25000000000000 : ℝ)*(sp3) + (36903639367/100000000000000 : ℝ)*(sp4) + (7338931323/50000000000000 : ℝ)*(sp7) + (1330341094683521/50000000000000 : ℝ)*(f.failure) + (1069896419309861/20000000000000 : ℝ)*(f.sum) + (24541253014149/7039000000000000000000000000 : ℝ)*base65 + (3152336633157360801/1759750000000000000000000000000000 : ℝ)*base67 + (11572599706982610801/1759750000000000000000000000000000 : ℝ)*base69 + (27384906477751110801/1759750000000000000000000000000000 : ℝ)*base71 + (38794067041/28156000000000000000000000 : ℝ)*base73 + (17350358071355610801/1759750000000000000000000000000000 : ℝ)*base75 + (23140676257169610801/1759750000000000000000000000000000 : ℝ)*base77 + (16760363746553610801/1759750000000000000000000000000000 : ℝ)*base79 + (7078606455551/3519500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (72187121/5000000000000000000000 : ℝ)*base90 + (72187121/5000000000000000000000 : ℝ)*base92 + (72187121/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (712331612120223724853543349/879875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (956836817/100000000000000 : ℝ)*(base19) + (718963171/100000000000000 : ℝ)*(base23) + (686757/12500000000000 : ℝ)*(upper3) + (10883107/12500000000000 : ℝ)*(lower4) + (28630027/20000000000000 : ℝ)*(upper5) + (2017660493590557/50000000000000 : ℝ)*(major0) + (2017660493590557/50000000000000 : ℝ)*(major1) + (2017660493590557/50000000000000 : ℝ)*(major2) + (4209928429/20000000000000 : ℝ)*(sp1) + (20180963009/100000000000000 : ℝ)*(sp2) + (5389871399101639/100000000000000 : ℝ)*(sp4) + (1347462348155669/25000000000000 : ℝ)*(sp5) + (5389850499175459/100000000000000 : ℝ)*(sp6) + (670192637068623/25000000000000 : ℝ)*(sp7) + (670192637068623/25000000000000 : ℝ)*(f.failure) + (5389871399101639/100000000000000 : ℝ)*(f.sum) + (26378503469541/7039000000000000000000000000 : ℝ)*base65 + (11585488887301277217/1759750000000000000000000000000000 : ℝ)*base68 + (11404198652173527217/1759750000000000000000000000000000 : ℝ)*base70 + (4618357190387222783/1759750000000000000000000000000000 : ℝ)*base71 + (11075961539827/7039000000000000000000000000 : ℝ)*base73 + (13886157784976972783/1759750000000000000000000000000000 : ℝ)*base75 + (116110722665527217/1759750000000000000000000000000000 : ℝ)*base78 + (15100375678039777217/1759750000000000000000000000000000 : ℝ)*base80 + (227021299289/879875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (23324577/2500000000000000000000 : ℝ)*base89 + (23324577/2500000000000000000000 : ℝ)*base91 + (23324577/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1196_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1196_s4_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140673513/10000000000 : ℝ)*x 0 + (1349855037/2500000000 : ℝ)*x 1 + (5259628781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140673513/10000000000 : ℝ)^8389 ≤ (6505839240791/50000000000000 : ℝ)^6341 := by
    have hnat : (2140673513 : ℕ)^8389*50000000000000^6341 ≤ 6505839240791^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140673513 10000000000 6505839240791 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349855037/2500000000 : ℝ)^8389 ≤ (11062194448491/25000000000000 : ℝ)^6341 := by
    have hnat : (1349855037 : ℕ)^8389*25000000000000^6341 ≤ 11062194448491^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349855037 2500000000 11062194448491 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259628781/10000000000 : ℝ)^8389 ≤ (42739543702023/100000000000000 : ℝ)^6341 := by
    have hnat : (5259628781 : ℕ)^8389*100000000000000^6341 ≤ 42739543702023^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259628781 10000000000 42739543702023 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140673513/10000000000 : ℝ), (1349855037/2500000000 : ℝ), (5259628781/10000000000 : ℝ)] ![(6505839240791/50000000000000 : ℝ), (11062194448491/25000000000000 : ℝ), (42739543702023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140673513/10000000000 : ℝ)|^8389 ≤ (6505839240791/50000000000000 : ℝ)^6341
        have hw : |(-2140673513/10000000000 : ℝ)|=(2140673513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349855037/2500000000 : ℝ)|^8389 ≤ (11062194448491/25000000000000 : ℝ)^6341
        have hw : |(1349855037/2500000000 : ℝ)|=(1349855037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259628781/10000000000 : ℝ)|^8389 ≤ (42739543702023/100000000000000 : ℝ)^6341
        have hw : |(5259628781/10000000000 : ℝ)|=(5259628781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336598247/2500000000 : ℝ)*x 0 + (-2211676001/10000000000 : ℝ)*x 1 + (5259629063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336598247/2500000000 : ℝ)^8389 ≤ (1746990994613/4000000000000 : ℝ)^6341 := by
    have hnat : (1336598247 : ℕ)^8389*4000000000000^6341 ≤ 1746990994613^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336598247 2500000000 1746990994613 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211676001/10000000000 : ℝ)^8389 ≤ (6792839192363/50000000000000 : ℝ)^6341 := by
    have hnat : (2211676001 : ℕ)^8389*50000000000000^6341 ≤ 6792839192363^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211676001 10000000000 6792839192363 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259629063/10000000000 : ℝ)^8389 ≤ (21369773366827/50000000000000 : ℝ)^6341 := by
    have hnat : (5259629063 : ℕ)^8389*50000000000000^6341 ≤ 21369773366827^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259629063 10000000000 21369773366827 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336598247/2500000000 : ℝ), (-2211676001/10000000000 : ℝ), (5259629063/10000000000 : ℝ)] ![(1746990994613/4000000000000 : ℝ), (6792839192363/50000000000000 : ℝ), (21369773366827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336598247/2500000000 : ℝ)|^8389 ≤ (1746990994613/4000000000000 : ℝ)^6341
        have hw : |(1336598247/2500000000 : ℝ)|=(1336598247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211676001/10000000000 : ℝ)|^8389 ≤ (6792839192363/50000000000000 : ℝ)^6341
        have hw : |(-2211676001/10000000000 : ℝ)|=(2211676001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259629063/10000000000 : ℝ)|^8389 ≤ (21369773366827/50000000000000 : ℝ)^6341
        have hw : |(5259629063/10000000000 : ℝ)|=(5259629063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346393049/10000000000 : ℝ)*x 0 + (5259628789/10000000000 : ℝ)*x 1 + (-1105838141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346393049/10000000000 : ℝ)^8389 ≤ (21837387762289/50000000000000 : ℝ)^6341 := by
    have hnat : (5346393049 : ℕ)^8389*50000000000000^6341 ≤ 21837387762289^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346393049 10000000000 21837387762289 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259628789/10000000000 : ℝ)^8389 ≤ (42739543788027/100000000000000 : ℝ)^6341 := by
    have hnat : (5259628789 : ℕ)^8389*100000000000000^6341 ≤ 42739543788027^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259628789 10000000000 42739543788027 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105838141/5000000000 : ℝ)^8389 ≤ (6792840334159/50000000000000 : ℝ)^6341 := by
    have hnat : (1105838141 : ℕ)^8389*50000000000000^6341 ≤ 6792840334159^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105838141 5000000000 6792840334159 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346393049/10000000000 : ℝ), (5259628789/10000000000 : ℝ), (-1105838141/5000000000 : ℝ)] ![(21837387762289/50000000000000 : ℝ), (42739543788027/100000000000000 : ℝ), (6792840334159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346393049/10000000000 : ℝ)|^8389 ≤ (21837387762289/50000000000000 : ℝ)^6341
        have hw : |(5346393049/10000000000 : ℝ)|=(5346393049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259628789/10000000000 : ℝ)|^8389 ≤ (42739543788027/100000000000000 : ℝ)^6341
        have hw : |(5259628789/10000000000 : ℝ)|=(5259628789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105838141/5000000000 : ℝ)|^8389 ≤ (6792840334159/50000000000000 : ℝ)^6341
        have hw : |(-1105838141/5000000000 : ℝ)|=(1105838141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178369023/5000000000 : ℝ)*x 0 + (1054608661/2500000000 : ℝ)*x 1 + (4499493977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178369023/5000000000 : ℝ)^8389 ≤ (33313382667901/100000000000000 : ℝ)^6341 := by
    have hnat : (2178369023 : ℕ)^8389*100000000000000^6341 ≤ 33313382667901^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178369023 5000000000 33313382667901 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054608661/2500000000 : ℝ)^8389 ≤ (15960763437849/50000000000000 : ℝ)^6341 := by
    have hnat : (1054608661 : ℕ)^8389*50000000000000^6341 ≤ 15960763437849^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054608661 2500000000 15960763437849 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499493977/10000000000 : ℝ)^8389 ≤ (34765090438287/100000000000000 : ℝ)^6341 := by
    have hnat : (4499493977 : ℕ)^8389*100000000000000^6341 ≤ 34765090438287^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499493977 10000000000 34765090438287 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178369023/5000000000 : ℝ), (1054608661/2500000000 : ℝ), (4499493977/10000000000 : ℝ)] ![(33313382667901/100000000000000 : ℝ), (15960763437849/50000000000000 : ℝ), (34765090438287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178369023/5000000000 : ℝ)|^8389 ≤ (33313382667901/100000000000000 : ℝ)^6341
        have hw : |(2178369023/5000000000 : ℝ)|=(2178369023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054608661/2500000000 : ℝ)|^8389 ≤ (15960763437849/50000000000000 : ℝ)^6341
        have hw : |(1054608661/2500000000 : ℝ)|=(1054608661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499493977/10000000000 : ℝ)|^8389 ≤ (34765090438287/100000000000000 : ℝ)^6341
        have hw : |(4499493977/10000000000 : ℝ)|=(4499493977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140680009/10000000000 : ℝ)*x 0 + (5260020827/10000000000 : ℝ)*x 1 + (5399026583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140680009/10000000000 : ℝ)^8389 ≤ (13011730718983/100000000000000 : ℝ)^6341 := by
    have hnat : (2140680009 : ℕ)^8389*100000000000000^6341 ≤ 13011730718983^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140680009 10000000000 13011730718983 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260020827/10000000000 : ℝ)^8389 ≤ (42743758429359/100000000000000 : ℝ)^6341 := by
    have hnat : (5260020827 : ℕ)^8389*100000000000000^6341 ≤ 42743758429359^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260020827 10000000000 42743758429359 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399026583/10000000000 : ℝ)^8389 ≤ (22122255420011/50000000000000 : ℝ)^6341 := by
    have hnat : (5399026583 : ℕ)^8389*50000000000000^6341 ≤ 22122255420011^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399026583 10000000000 22122255420011 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140680009/10000000000 : ℝ), (5260020827/10000000000 : ℝ), (5399026583/10000000000 : ℝ)] ![(13011730718983/100000000000000 : ℝ), (42743758429359/100000000000000 : ℝ), (22122255420011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140680009/10000000000 : ℝ)|^8389 ≤ (13011730718983/100000000000000 : ℝ)^6341
        have hw : |(-2140680009/10000000000 : ℝ)|=(2140680009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260020827/10000000000 : ℝ)|^8389 ≤ (42743758429359/100000000000000 : ℝ)^6341
        have hw : |(5260020827/10000000000 : ℝ)|=(5260020827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399026583/10000000000 : ℝ)|^8389 ≤ (22122255420011/50000000000000 : ℝ)^6341
        have hw : |(5399026583/10000000000 : ℝ)|=(5399026583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310839589/10000000000 : ℝ)*x 0 + (-207227893/1000000000 : ℝ)*x 1 + (5399026363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310839589/10000000000 : ℝ)^8389 ≤ (10822736855359/25000000000000 : ℝ)^6341 := by
    have hnat : (5310839589 : ℕ)^8389*25000000000000^6341 ≤ 10822736855359^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310839589 10000000000 10822736855359 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207227893/1000000000 : ℝ)^8389 ≤ (12464544108451/100000000000000 : ℝ)^6341 := by
    have hnat : (207227893 : ℕ)^8389*100000000000000^6341 ≤ 12464544108451^6341*1000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207227893 1000000000 12464544108451 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399026363/10000000000 : ℝ)^8389 ≤ (44244508454853/100000000000000 : ℝ)^6341 := by
    have hnat : (5399026363 : ℕ)^8389*100000000000000^6341 ≤ 44244508454853^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399026363 10000000000 44244508454853 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310839589/10000000000 : ℝ), (-207227893/1000000000 : ℝ), (5399026363/10000000000 : ℝ)] ![(10822736855359/25000000000000 : ℝ), (12464544108451/100000000000000 : ℝ), (44244508454853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310839589/10000000000 : ℝ)|^8389 ≤ (10822736855359/25000000000000 : ℝ)^6341
        have hw : |(5310839589/10000000000 : ℝ)|=(5310839589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207227893/1000000000 : ℝ)|^8389 ≤ (12464544108451/100000000000000 : ℝ)^6341
        have hw : |(-207227893/1000000000 : ℝ)|=(207227893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399026363/10000000000 : ℝ)|^8389 ≤ (44244508454853/100000000000000 : ℝ)^6341
        have hw : |(5399026363/10000000000 : ℝ)|=(5399026363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310839277/10000000000 : ℝ)*x 0 + (1349756723/2500000000 : ℝ)*x 1 + (-259034829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310839277/10000000000 : ℝ)^8389 ≤ (21645472028389/50000000000000 : ℝ)^6341 := by
    have hnat : (5310839277 : ℕ)^8389*50000000000000^6341 ≤ 21645472028389^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310839277 10000000000 21645472028389 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349756723/2500000000 : ℝ)^8389 ≤ (44244514190099/100000000000000 : ℝ)^6341 := by
    have hnat : (1349756723 : ℕ)^8389*100000000000000^6341 ≤ 44244514190099^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349756723 2500000000 44244514190099 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259034829/1250000000 : ℝ)^8389 ≤ (2492908347419/20000000000000 : ℝ)^6341 := by
    have hnat : (259034829 : ℕ)^8389*20000000000000^6341 ≤ 2492908347419^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259034829 1250000000 2492908347419 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310839277/10000000000 : ℝ), (1349756723/2500000000 : ℝ), (-259034829/1250000000 : ℝ)] ![(21645472028389/50000000000000 : ℝ), (44244514190099/100000000000000 : ℝ), (2492908347419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310839277/10000000000 : ℝ)|^8389 ≤ (21645472028389/50000000000000 : ℝ)^6341
        have hw : |(5310839277/10000000000 : ℝ)|=(5310839277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349756723/2500000000 : ℝ)|^8389 ≤ (44244514190099/100000000000000 : ℝ)^6341
        have hw : |(1349756723/2500000000 : ℝ)|=(1349756723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259034829/1250000000 : ℝ)|^8389 ≤ (2492908347419/20000000000000 : ℝ)^6341
        have hw : |(-259034829/1250000000 : ℝ)|=(259034829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s4_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089187829/2500000000 : ℝ)*x 0 + (899741293/2000000000 : ℝ)*x 1 + (2109612639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089187829/2500000000 : ℝ)^8389 ≤ (33313516907567/100000000000000 : ℝ)^6341 := by
    have hnat : (1089187829 : ℕ)^8389*100000000000000^6341 ≤ 33313516907567^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089187829 2500000000 33313516907567 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899741293/2000000000 : ℝ)^8389 ≤ (34757040787603/100000000000000 : ℝ)^6341 := by
    have hnat : (899741293 : ℕ)^8389*100000000000000^6341 ≤ 34757040787603^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899741293 2000000000 34757040787603 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109612639/5000000000 : ℝ)^8389 ≤ (31929442285477/100000000000000 : ℝ)^6341 := by
    have hnat : (2109612639 : ℕ)^8389*100000000000000^6341 ≤ 31929442285477^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109612639 5000000000 31929442285477 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089187829/2500000000 : ℝ), (899741293/2000000000 : ℝ), (2109612639/5000000000 : ℝ)] ![(33313516907567/100000000000000 : ℝ), (34757040787603/100000000000000 : ℝ), (31929442285477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089187829/2500000000 : ℝ)|^8389 ≤ (33313516907567/100000000000000 : ℝ)^6341
        have hw : |(1089187829/2500000000 : ℝ)|=(1089187829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899741293/2000000000 : ℝ)|^8389 ≤ (34757040787603/100000000000000 : ℝ)^6341
        have hw : |(899741293/2000000000 : ℝ)|=(899741293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109612639/5000000000 : ℝ)|^8389 ≤ (31929442285477/100000000000000 : ℝ)^6341
        have hw : |(2109612639/5000000000 : ℝ)|=(2109612639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5637/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10789/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10789/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10789/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10789/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10789/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10789/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10789/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (10949090630573091/100000000000000000000 : ℝ) := by
    have hpowers : (10789/100000 : ℝ)^2097 ≤ (10949090630573091/100000000000000000000 : ℝ)^512 := by
      have hnat : (10789 : ℕ)^2097*100000000000000000000^512 ≤ 10949090630573091^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10789 100000 10949090630573091 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10789/100000 : ℝ)) (X := (10949090630573091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2949/20000 : ℝ) ^ (2097/512 : ℝ) ≤ (39356440673469217/100000000000000000000 : ℝ) := by
    have hpowers : (2949/20000 : ℝ)^2097 ≤ (39356440673469217/100000000000000000000 : ℝ)^512 := by
      have hnat : (2949 : ℕ)^2097*100000000000000000000^512 ≤ 39356440673469217^512*20000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2949 20000 39356440673469217 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2949/20000 : ℝ)) (X := (39356440673469217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010949090630573091/50000000000000000000 : ℝ) ≤ (10000534618076067/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50010949090630573091/50000000000000000000 : ℝ)^512 ≤ (10000534618076067/10000000000000000 : ℝ)^2097 := by
      have hnat : (50010949090630573091 : ℕ)^512*10000000000000000^2097 ≤ 10000534618076067^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010949090630573091 50000000000000000000 10000534618076067 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534618076067/10000000000000000 : ℝ)) (X := (50010949090630573091/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012576382826010577/25000000000000000000 : ℝ) ≤ (10001228017967697/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25012576382826010577/25000000000000000000 : ℝ)^512 ≤ (10001228017967697/10000000000000000 : ℝ)^2097 := by
      have hnat : (25012576382826010577 : ℕ)^512*10000000000000000^2097 ≤ 10001228017967697^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012576382826010577 25000000000000000000 10001228017967697 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228017967697/10000000000000000 : ℝ)) (X := (25012576382826010577/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039356440673469217/50000000000000000000 : ℝ) ≤ (10001921417859327/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50039356440673469217/50000000000000000000 : ℝ)^512 ≤ (10001921417859327/10000000000000000 : ℝ)^2097 := by
      have hnat : (50039356440673469217 : ℕ)^512*10000000000000000^2097 ≤ 10001921417859327^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039356440673469217 50000000000000000000 10001921417859327 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001921417859327/10000000000000000 : ℝ)) (X := (50039356440673469217/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10949090630573091/100000000000000000000 : ℝ) ≤ ((2471697047890458057/2472500000000000000 : ℝ)+2*(69339989163/39560000000000 : ℝ)*(10789/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (2471697047890458057/2472500000000000000 : ℝ)+2*(69339989163/39560000000000 : ℝ)*(10789/100000 : ℝ)=(10000534618076067/10000000000000000 : ℝ) by norm_num, show 1+2*(10949090630573091/100000000000000000000 : ℝ)=(50010949090630573091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39356440673469217/100000000000000000000 : ℝ)+(10949090630573091/100000000000000000000 : ℝ) ≤ ((2471697047890458057/2472500000000000000 : ℝ)+(69339989163/39560000000000 : ℝ)*((2949/20000 : ℝ)+(10789/100000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (2471697047890458057/2472500000000000000 : ℝ)+(69339989163/39560000000000 : ℝ)*((2949/20000 : ℝ)+(10789/100000 : ℝ))=(10001228017967697/10000000000000000 : ℝ) by norm_num, show 1+(39356440673469217/100000000000000000000 : ℝ)+(10949090630573091/100000000000000000000 : ℝ)=(25012576382826010577/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39356440673469217/100000000000000000000 : ℝ) ≤ ((2471697047890458057/2472500000000000000 : ℝ)+2*(69339989163/39560000000000 : ℝ)*(2949/20000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (2471697047890458057/2472500000000000000 : ℝ)+2*(69339989163/39560000000000 : ℝ)*(2949/20000 : ℝ)=(10001921417859327/10000000000000000 : ℝ) by norm_num, show 1+2*(39356440673469217/100000000000000000000 : ℝ)=(50039356440673469217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2471697047890458057/2472500000000000000 : ℝ)*(X 1 0+X 2 0)+(69339989163/39560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (10789/100000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (2471697047890458057/2472500000000000000 : ℝ)) (alpha := (69339989163/39560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2471697047890458057/2472500000000000000 : ℝ)*(X 0 1+X 2 1)+(69339989163/39560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (10789/100000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (2471697047890458057/2472500000000000000 : ℝ)) (alpha := (69339989163/39560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2471697047890458057/2472500000000000000 : ℝ)*(X 0 2+X 1 2)+(69339989163/39560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (10789/100000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (2471697047890458057/2472500000000000000 : ℝ)) (alpha := (69339989163/39560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2140673513/10000000000 : ℝ)*X 0 0+(1349855037/2500000000 : ℝ)*X 0 1+(5259628781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336598247/2500000000 : ℝ)*X 1 0+(-2211676001/10000000000 : ℝ)*X 1 1+(5259629063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346393049/10000000000 : ℝ)*X 2 0+(5259628789/10000000000 : ℝ)*X 2 1+(-1105838141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178369023/5000000000 : ℝ)*X 0 0+(1054608661/2500000000 : ℝ)*X 0 1+(4499493977/10000000000 : ℝ)*X 0 2+(2178369023/5000000000 : ℝ)*X 1 0+(1054608661/2500000000 : ℝ)*X 1 1+(4499493977/10000000000 : ℝ)*X 1 2+(2178369023/5000000000 : ℝ)*X 2 0+(1054608661/2500000000 : ℝ)*X 2 1+(4499493977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140680009/10000000000 : ℝ)*X 0 0+(5260020827/10000000000 : ℝ)*X 0 1+(5399026583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310839589/10000000000 : ℝ)*X 1 0+(-207227893/1000000000 : ℝ)*X 1 1+(5399026363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310839277/10000000000 : ℝ)*X 2 0+(1349756723/2500000000 : ℝ)*X 2 1+(-259034829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089187829/2500000000 : ℝ)*X 0 0+(899741293/2000000000 : ℝ)*X 0 1+(2109612639/5000000000 : ℝ)*X 0 2+(1089187829/2500000000 : ℝ)*X 1 0+(899741293/2000000000 : ℝ)*X 1 1+(2109612639/5000000000 : ℝ)*X 1 2+(1089187829/2500000000 : ℝ)*X 2 0+(899741293/2000000000 : ℝ)*X 2 1+(2109612639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (450000038215491249005587953/123625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (804617459/50000000000000 : ℝ)*(base19) + (1770113603/100000000000000 : ℝ)*(base23) + (46931161/100000000000000 : ℝ)*(upper2) + (170916971/50000000000000 : ℝ)*(upper3) + (227809/5000000000000 : ℝ)*(upper4) + (5355816758673357/100000000000000 : ℝ)*(major0) + (5355816758673357/100000000000000 : ℝ)*(major1) + (5355816758673357/100000000000000 : ℝ)*(major2) + (3576788939729593/50000000000000 : ℝ)*(sp0) + (7153620943472133/100000000000000 : ℝ)*(sp1) + (894202597824181/12500000000000 : ℝ)*(sp2) + (177899300648437/5000000000000 : ℝ)*(sp3) + (8934649573/20000000000000 : ℝ)*(sp4) + (24830336221/100000000000000 : ℝ)*(sp7) + (3558010843304961/100000000000000 : ℝ)*(f.failure) + (7153622552707051/100000000000000 : ℝ)*(f.sum) + (19252133492997/1978000000000000000000000000 : ℝ)*base65 + (1368894062580824849/247250000000000000000000000000000 : ℝ)*base67 + (3509673629201074849/247250000000000000000000000000000 : ℝ)*base69 + (3435349957528824849/247250000000000000000000000000000 : ℝ)*base71 + (335801764883/395600000000000000000000000 : ℝ)*base73 + (291541397299425151/247250000000000000000000000000000 : ℝ)*base76 + (2363387804285824849/247250000000000000000000000000000 : ℝ)*base77 + (2418533505549425151/247250000000000000000000000000000 : ℝ)*base80 + (4474467734799/395600000000000000000000000 : ℝ)*base81 + (51912561/10000000000000000000000 : ℝ)*base90 + (51912561/10000000000000000000000 : ℝ)*base92 + (51912561/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (356510632996975512534136737/30906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1081682989/50000000000000 : ℝ)*(base19) + (411095699/20000000000000 : ℝ)*(base23) + (207245113/50000000000000 : ℝ)*(upper3) + (39658011/50000000000000 : ℝ)*(lower4) + (52485069/25000000000000 : ℝ)*(upper5) + (1346499197050753/25000000000000 : ℝ)*(major0) + (1346499197050753/25000000000000 : ℝ)*(major1) + (1346499197050753/25000000000000 : ℝ)*(major2) + (15158192817/50000000000000 : ℝ)*(sp1) + (27510775337/50000000000000 : ℝ)*(sp2) + (1798483239024997/25000000000000 : ℝ)*(sp4) + (57551203810787/800000000000 : ℝ)*(sp5) + (7193875879070819/100000000000000 : ℝ)*(sp6) + (3578060235798437/100000000000000 : ℝ)*(sp7) + (3578060235798437/100000000000000 : ℝ)*(f.failure) + (1798483239024997/25000000000000 : ℝ)*(f.sum) + (437429967661/494500000000000000000000000 : ℝ)*base66 + (444215790073641921/61812500000000000000000000000000 : ℝ)*base67 + (197656470029829421/61812500000000000000000000000000 : ℝ)*base69 + (1332362510252266921/61812500000000000000000000000000 : ℝ)*base71 + (2543288613509/989000000000000000000000000 : ℝ)*base73 + (610932008239358079/61812500000000000000000000000000 : ℝ)*base76 + (512897469929891921/61812500000000000000000000000000 : ℝ)*base77 + (85626635373983079/61812500000000000000000000000000 : ℝ)*base80 + (934908118597/247250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8312363/10000000000000000000000 : ℝ)*base89 + (8312363/10000000000000000000000 : ℝ)*base91 + (8312363/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1196_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1196_s5_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141196977/10000000000 : ℝ)*x 0 + (5393536799/10000000000 : ℝ)*x 1 + (1316292157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141196977/10000000000 : ℝ)^8389 ≤ (13015888066717/100000000000000 : ℝ)^6341 := by
    have hnat : (2141196977 : ℕ)^8389*100000000000000^6341 ≤ 13015888066717^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141196977 10000000000 13015888066717 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393536799/10000000000 : ℝ)^8389 ≤ (8837000432589/20000000000000 : ℝ)^6341 := by
    have hnat : (5393536799 : ℕ)^8389*20000000000000^6341 ≤ 8837000432589^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393536799 10000000000 8837000432589 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316292157/2500000000 : ℝ)^8389 ≤ (1337472179941/3125000000000 : ℝ)^6341 := by
    have hnat : (1316292157 : ℕ)^8389*3125000000000^6341 ≤ 1337472179941^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316292157 2500000000 1337472179941 3125000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141196977/10000000000 : ℝ), (5393536799/10000000000 : ℝ), (1316292157/2500000000 : ℝ)] ![(13015888066717/100000000000000 : ℝ), (8837000432589/20000000000000 : ℝ), (1337472179941/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141196977/10000000000 : ℝ)|^8389 ≤ (13015888066717/100000000000000 : ℝ)^6341
        have hw : |(-2141196977/10000000000 : ℝ)|=(2141196977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393536799/10000000000 : ℝ)|^8389 ≤ (8837000432589/20000000000000 : ℝ)^6341
        have hw : |(5393536799/10000000000 : ℝ)|=(5393536799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316292157/2500000000 : ℝ)|^8389 ≤ (1337472179941/3125000000000 : ℝ)^6341
        have hw : |(1316292157/2500000000 : ℝ)|=(1316292157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336227803/2500000000 : ℝ)*x 0 + (-1103157467/5000000000 : ℝ)*x 1 + (2632584359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336227803/2500000000 : ℝ)^8389 ≤ (21829380699433/50000000000000 : ℝ)^6341 := by
    have hnat : (1336227803 : ℕ)^8389*50000000000000^6341 ≤ 21829380699433^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336227803 2500000000 21829380699433 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103157467/5000000000 : ℝ)^8389 ≤ (2708425572429/20000000000000 : ℝ)^6341 := by
    have hnat : (1103157467 : ℕ)^8389*20000000000000^6341 ≤ 2708425572429^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103157467 5000000000 2708425572429 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632584359/5000000000 : ℝ)^8389 ≤ (42799110725983/100000000000000 : ℝ)^6341 := by
    have hnat : (2632584359 : ℕ)^8389*100000000000000^6341 ≤ 42799110725983^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632584359 5000000000 42799110725983 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336227803/2500000000 : ℝ), (-1103157467/5000000000 : ℝ), (2632584359/5000000000 : ℝ)] ![(21829380699433/50000000000000 : ℝ), (2708425572429/20000000000000 : ℝ), (42799110725983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336227803/2500000000 : ℝ)|^8389 ≤ (21829380699433/50000000000000 : ℝ)^6341
        have hw : |(1336227803/2500000000 : ℝ)|=(1336227803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103157467/5000000000 : ℝ)|^8389 ≤ (2708425572429/20000000000000 : ℝ)^6341
        have hw : |(-1103157467/5000000000 : ℝ)|=(1103157467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632584359/5000000000 : ℝ)|^8389 ≤ (42799110725983/100000000000000 : ℝ)^6341
        have hw : |(2632584359/5000000000 : ℝ)|=(2632584359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672455591/5000000000 : ℝ)*x 0 + (5265168697/10000000000 : ℝ)*x 1 + (-2206315001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672455591/5000000000 : ℝ)^8389 ≤ (2728672567167/6250000000000 : ℝ)^6341 := by
    have hnat : (2672455591 : ℕ)^8389*6250000000000^6341 ≤ 2728672567167^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672455591 5000000000 2728672567167 6250000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265168697/10000000000 : ℝ)^8389 ≤ (21399555250073/50000000000000 : ℝ)^6341 := by
    have hnat : (5265168697 : ℕ)^8389*50000000000000^6341 ≤ 21399555250073^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265168697 10000000000 21399555250073 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206315001/10000000000 : ℝ)^8389 ≤ (2708425681241/20000000000000 : ℝ)^6341 := by
    have hnat : (2206315001 : ℕ)^8389*20000000000000^6341 ≤ 2708425681241^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206315001 10000000000 2708425681241 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672455591/5000000000 : ℝ), (5265168697/10000000000 : ℝ), (-2206315001/10000000000 : ℝ)] ![(2728672567167/6250000000000 : ℝ), (21399555250073/50000000000000 : ℝ), (2708425681241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672455591/5000000000 : ℝ)|^8389 ≤ (2728672567167/6250000000000 : ℝ)^6341
        have hw : |(2672455591/5000000000 : ℝ)|=(2672455591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265168697/10000000000 : ℝ)|^8389 ≤ (21399555250073/50000000000000 : ℝ)^6341
        have hw : |(5265168697/10000000000 : ℝ)|=(5265168697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206315001/10000000000 : ℝ)|^8389 ≤ (2708425681241/20000000000000 : ℝ)^6341
        have hw : |(-2206315001/10000000000 : ℝ)|=(2206315001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178523347/5000000000 : ℝ)*x 0 + (264367389/625000000 : ℝ)*x 1 + (2243985599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178523347/5000000000 : ℝ)^8389 ≤ (16658252496651/50000000000000 : ℝ)^6341 := by
    have hnat : (2178523347 : ℕ)^8389*50000000000000^6341 ≤ 16658252496651^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178523347 5000000000 16658252496651 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264367389/625000000 : ℝ)^8389 ≤ (32036140640979/100000000000000 : ℝ)^6341 := by
    have hnat : (264367389 : ℕ)^8389*100000000000000^6341 ≤ 32036140640979^6341*625000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264367389 625000000 32036140640979 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243985599/5000000000 : ℝ)^8389 ≤ (6929470869293/20000000000000 : ℝ)^6341 := by
    have hnat : (2243985599 : ℕ)^8389*20000000000000^6341 ≤ 6929470869293^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243985599 5000000000 6929470869293 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178523347/5000000000 : ℝ), (264367389/625000000 : ℝ), (2243985599/5000000000 : ℝ)] ![(16658252496651/50000000000000 : ℝ), (32036140640979/100000000000000 : ℝ), (6929470869293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178523347/5000000000 : ℝ)|^8389 ≤ (16658252496651/50000000000000 : ℝ)^6341
        have hw : |(2178523347/5000000000 : ℝ)|=(2178523347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264367389/625000000 : ℝ)|^8389 ≤ (32036140640979/100000000000000 : ℝ)^6341
        have hw : |(264367389/625000000 : ℝ)|=(264367389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243985599/5000000000 : ℝ)|^8389 ≤ (6929470869293/20000000000000 : ℝ)^6341
        have hw : |(2243985599/5000000000 : ℝ)|=(2243985599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141202071/10000000000 : ℝ)*x 0 + (2632749629/5000000000 : ℝ)*x 1 + (1078640989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141202071/10000000000 : ℝ)^8389 ≤ (2603185806641/20000000000000 : ℝ)^6341 := by
    have hnat : (2141202071 : ℕ)^8389*20000000000000^6341 ≤ 2603185806641^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141202071 10000000000 2603185806641 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632749629/5000000000 : ℝ)^8389 ≤ (1712106617159/4000000000000 : ℝ)^6341 := by
    have hnat : (2632749629 : ℕ)^8389*4000000000000^6341 ≤ 1712106617159^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632749629 5000000000 1712106617159 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078640989/2000000000 : ℝ)^8389 ≤ (11045351381881/25000000000000 : ℝ)^6341 := by
    have hnat : (1078640989 : ℕ)^8389*25000000000000^6341 ≤ 11045351381881^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078640989 2000000000 11045351381881 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141202071/10000000000 : ℝ), (2632749629/5000000000 : ℝ), (1078640989/2000000000 : ℝ)] ![(2603185806641/20000000000000 : ℝ), (1712106617159/4000000000000 : ℝ), (11045351381881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141202071/10000000000 : ℝ)|^8389 ≤ (2603185806641/20000000000000 : ℝ)^6341
        have hw : |(-2141202071/10000000000 : ℝ)|=(2141202071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632749629/5000000000 : ℝ)|^8389 ≤ (1712106617159/4000000000000 : ℝ)^6341
        have hw : |(2632749629/5000000000 : ℝ)|=(2632749629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078640989/2000000000 : ℝ)|^8389 ≤ (11045351381881/25000000000000 : ℝ)^6341
        have hw : |(1078640989/2000000000 : ℝ)|=(1078640989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062452357/2000000000 : ℝ)*x 0 + (-2078278719/10000000000 : ℝ)*x 1 + (2696602427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062452357/2000000000 : ℝ)^8389 ≤ (21653142637377/50000000000000 : ℝ)^6341 := by
    have hnat : (1062452357 : ℕ)^8389*50000000000000^6341 ≤ 21653142637377^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062452357 2000000000 21653142637377 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078278719/10000000000 : ℝ)^8389 ≤ (24438105811/195312500000 : ℝ)^6341 := by
    have hnat : (2078278719 : ℕ)^8389*195312500000^6341 ≤ 24438105811^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078278719 10000000000 24438105811 195312500000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696602427/5000000000 : ℝ)^8389 ≤ (1767256181651/4000000000000 : ℝ)^6341 := by
    have hnat : (2696602427 : ℕ)^8389*4000000000000^6341 ≤ 1767256181651^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696602427 5000000000 1767256181651 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062452357/2000000000 : ℝ), (-2078278719/10000000000 : ℝ), (2696602427/5000000000 : ℝ)] ![(21653142637377/50000000000000 : ℝ), (24438105811/195312500000 : ℝ), (1767256181651/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062452357/2000000000 : ℝ)|^8389 ≤ (21653142637377/50000000000000 : ℝ)^6341
        have hw : |(1062452357/2000000000 : ℝ)|=(1062452357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078278719/10000000000 : ℝ)|^8389 ≤ (24438105811/195312500000 : ℝ)^6341
        have hw : |(-2078278719/10000000000 : ℝ)|=(2078278719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696602427/5000000000 : ℝ)|^8389 ≤ (1767256181651/4000000000000 : ℝ)^6341
        have hw : |(2696602427/5000000000 : ℝ)|=(2696602427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312261843/10000000000 : ℝ)*x 0 + (1348301203/2500000000 : ℝ)*x 1 + (-2078278697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312261843/10000000000 : ℝ)^8389 ≤ (4330628590029/10000000000000 : ℝ)^6341 := by
    have hnat : (5312261843 : ℕ)^8389*10000000000000^6341 ≤ 4330628590029^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312261843 10000000000 4330628590029 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348301203/2500000000 : ℝ)^8389 ≤ (44181404086083/100000000000000 : ℝ)^6341 := by
    have hnat : (1348301203 : ℕ)^8389*100000000000000^6341 ≤ 44181404086083^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348301203 2500000000 44181404086083 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078278697/10000000000 : ℝ)^8389 ≤ (6256155000001/50000000000000 : ℝ)^6341 := by
    have hnat : (2078278697 : ℕ)^8389*50000000000000^6341 ≤ 6256155000001^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078278697 10000000000 6256155000001 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312261843/10000000000 : ℝ), (1348301203/2500000000 : ℝ), (-2078278697/10000000000 : ℝ)] ![(4330628590029/10000000000000 : ℝ), (44181404086083/100000000000000 : ℝ), (6256155000001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312261843/10000000000 : ℝ)|^8389 ≤ (4330628590029/10000000000000 : ℝ)^6341
        have hw : |(5312261843/10000000000 : ℝ)|=(5312261843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348301203/2500000000 : ℝ)|^8389 ≤ (44181404086083/100000000000000 : ℝ)^6341
        have hw : |(1348301203/2500000000 : ℝ)|=(1348301203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078278697/10000000000 : ℝ)|^8389 ≤ (6256155000001/50000000000000 : ℝ)^6341
        have hw : |(-2078278697/10000000000 : ℝ)|=(2078278697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s5_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357057101/10000000000 : ℝ)*x 0 + (2243653283/5000000000 : ℝ)*x 1 + (4230545153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357057101/10000000000 : ℝ)^8389 ≤ (33316610273183/100000000000000 : ℝ)^6341 := by
    have hnat : (4357057101 : ℕ)^8389*100000000000000^6341 ≤ 33316610273183^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357057101 10000000000 33316610273183 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243653283/5000000000 : ℝ)^8389 ≤ (34640566323257/100000000000000 : ℝ)^6341 := by
    have hnat : (2243653283 : ℕ)^8389*100000000000000^6341 ≤ 34640566323257^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243653283 5000000000 34640566323257 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230545153/10000000000 : ℝ)^8389 ≤ (4005352924283/12500000000000 : ℝ)^6341 := by
    have hnat : (4230545153 : ℕ)^8389*12500000000000^6341 ≤ 4005352924283^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230545153 10000000000 4005352924283 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357057101/10000000000 : ℝ), (2243653283/5000000000 : ℝ), (4230545153/10000000000 : ℝ)] ![(33316610273183/100000000000000 : ℝ), (34640566323257/100000000000000 : ℝ), (4005352924283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357057101/10000000000 : ℝ)|^8389 ≤ (33316610273183/100000000000000 : ℝ)^6341
        have hw : |(4357057101/10000000000 : ℝ)|=(4357057101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243653283/5000000000 : ℝ)|^8389 ≤ (34640566323257/100000000000000 : ℝ)^6341
        have hw : |(2243653283/5000000000 : ℝ)|=(2243653283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230545153/10000000000 : ℝ)|^8389 ≤ (4005352924283/12500000000000 : ℝ)^6341
        have hw : |(4230545153/10000000000 : ℝ)|=(4230545153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (356/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14111/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5637/50000 : ℝ) ^ (2097/512 : ℝ) ≤ (6554854131138407/50000000000000000000 : ℝ) := by
    have hpowers : (5637/50000 : ℝ)^2097 ≤ (6554854131138407/50000000000000000000 : ℝ)^512 := by
      have hnat : (5637 : ℕ)^2097*50000000000000000000^512 ≤ 6554854131138407^512*50000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5637 50000 6554854131138407 50000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5637/50000 : ℝ)) (X := (6554854131138407/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (2097/512 : ℝ) ≤ (17036232347224623/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^2097 ≤ (17036232347224623/50000000000000000000 : ℝ)^512 := by
      have hnat : (2847 : ℕ)^2097*50000000000000000000^512 ≤ 17036232347224623^512*20000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17036232347224623 50000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17036232347224623/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006554854131138407/25000000000000000000 : ℝ) ≤ (10000640105448973/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25006554854131138407/25000000000000000000 : ℝ)^512 ≤ (10000640105448973/10000000000000000 : ℝ)^2097 := by
      have hnat : (25006554854131138407 : ℕ)^512*10000000000000000^2097 ≤ 10000640105448973^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006554854131138407 25000000000000000000 10000640105448973 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000640105448973/10000000000000000 : ℝ)) (X := (25006554854131138407/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002359108647836303/5000000000000000000 : ℝ) ≤ (250028794666463/250000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (5002359108647836303/5000000000000000000 : ℝ)^512 ≤ (250028794666463/250000000000000 : ℝ)^2097 := by
      have hnat : (5002359108647836303 : ℕ)^512*250000000000000^2097 ≤ 250028794666463^2097*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002359108647836303 5000000000000000000 250028794666463 250000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250028794666463/250000000000000 : ℝ)) (X := (5002359108647836303/5000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017036232347224623/25000000000000000000 : ℝ) ≤ (10001663467868067/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25017036232347224623/25000000000000000000 : ℝ)^512 ≤ (10001663467868067/10000000000000000 : ℝ)^2097 := by
      have hnat : (25017036232347224623 : ℕ)^512*10000000000000000^2097 ≤ 10001663467868067^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017036232347224623 25000000000000000000 10001663467868067 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001663467868067/10000000000000000 : ℝ)) (X := (25017036232347224623/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6554854131138407/50000000000000000000 : ℝ) ≤ ((9866785988107181099/9870000000000000000 : ℝ)+2*(511681209547/296100000000000 : ℝ)*(5637/50000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (9866785988107181099/9870000000000000000 : ℝ)+2*(511681209547/296100000000000 : ℝ)*(5637/50000 : ℝ)=(10000640105448973/10000000000000000 : ℝ) by norm_num, show 1+2*(6554854131138407/50000000000000000000 : ℝ)=(25006554854131138407/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17036232347224623/50000000000000000000 : ℝ)+(6554854131138407/50000000000000000000 : ℝ) ≤ ((9866785988107181099/9870000000000000000 : ℝ)+(511681209547/296100000000000 : ℝ)*((2847/20000 : ℝ)+(5637/50000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (9866785988107181099/9870000000000000000 : ℝ)+(511681209547/296100000000000 : ℝ)*((2847/20000 : ℝ)+(5637/50000 : ℝ))=(250028794666463/250000000000000 : ℝ) by norm_num, show 1+(17036232347224623/50000000000000000000 : ℝ)+(6554854131138407/50000000000000000000 : ℝ)=(5002359108647836303/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17036232347224623/50000000000000000000 : ℝ) ≤ ((9866785988107181099/9870000000000000000 : ℝ)+2*(511681209547/296100000000000 : ℝ)*(2847/20000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (9866785988107181099/9870000000000000000 : ℝ)+2*(511681209547/296100000000000 : ℝ)*(2847/20000 : ℝ)=(10001663467868067/10000000000000000 : ℝ) by norm_num, show 1+2*(17036232347224623/50000000000000000000 : ℝ)=(25017036232347224623/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9866785988107181099/9870000000000000000 : ℝ)*(X 1 0+X 2 0)+(511681209547/296100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (9866785988107181099/9870000000000000000 : ℝ)) (alpha := (511681209547/296100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9866785988107181099/9870000000000000000 : ℝ)*(X 0 1+X 2 1)+(511681209547/296100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (9866785988107181099/9870000000000000000 : ℝ)) (alpha := (511681209547/296100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9866785988107181099/9870000000000000000 : ℝ)*(X 0 2+X 1 2)+(511681209547/296100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (9866785988107181099/9870000000000000000 : ℝ)) (alpha := (511681209547/296100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141196977/10000000000 : ℝ)*X 0 0+(5393536799/10000000000 : ℝ)*X 0 1+(1316292157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336227803/2500000000 : ℝ)*X 1 0+(-1103157467/5000000000 : ℝ)*X 1 1+(2632584359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672455591/5000000000 : ℝ)*X 2 0+(5265168697/10000000000 : ℝ)*X 2 1+(-2206315001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178523347/5000000000 : ℝ)*X 0 0+(264367389/625000000 : ℝ)*X 0 1+(2243985599/5000000000 : ℝ)*X 0 2+(2178523347/5000000000 : ℝ)*X 1 0+(264367389/625000000 : ℝ)*X 1 1+(2243985599/5000000000 : ℝ)*X 1 2+(2178523347/5000000000 : ℝ)*X 2 0+(264367389/625000000 : ℝ)*X 2 1+(2243985599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2141202071/10000000000 : ℝ)*X 0 0+(2632749629/5000000000 : ℝ)*X 0 1+(1078640989/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062452357/2000000000 : ℝ)*X 1 0+(-2078278719/10000000000 : ℝ)*X 1 1+(2696602427/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312261843/10000000000 : ℝ)*X 2 0+(1348301203/2500000000 : ℝ)*X 2 1+(-2078278697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357057101/10000000000 : ℝ)*X 0 0+(2243653283/5000000000 : ℝ)*X 0 1+(4230545153/10000000000 : ℝ)*X 0 2+(4357057101/10000000000 : ℝ)*X 1 0+(2243653283/5000000000 : ℝ)*X 1 1+(4230545153/10000000000 : ℝ)*X 1 2+(4357057101/10000000000 : ℝ)*X 2 0+(2243653283/5000000000 : ℝ)*X 2 1+(4230545153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16887954343973881934249/2467500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1109623733/100000000000000 : ℝ)*(base19) + (1030058951/100000000000000 : ℝ)*(base23) + (1915617/10000000000000 : ℝ)*(lower2) + (162151999/100000000000000 : ℝ)*(upper3) + (254311/1250000000000 : ℝ)*(upper5) + (364524315129529/6250000000000 : ℝ)*(major0) + (364524315129529/6250000000000 : ℝ)*(major1) + (364524315129529/6250000000000 : ℝ)*(major2) + (3895066792054351/50000000000000 : ℝ)*(sp0) + (3895083160082517/50000000000000 : ℝ)*(sp1) + (973770799966227/12500000000000 : ℝ)*(sp2) + (1937295065988339/50000000000000 : ℝ)*(sp3) + (6769136013/20000000000000 : ℝ)*(sp4) + (10147120473/50000000000000 : ℝ)*(sp7) + (1937305213108811/50000000000000 : ℝ)*(f.failure) + (7790167429788767/100000000000000 : ℝ)*(f.sum) + (109821401457437/14805000000000000000000000000 : ℝ)*base66 + (1575224248264517113/185062500000000000000000000000000 : ℝ)*base67 + (456179202089079613/185062500000000000000000000000000 : ℝ)*base69 + (50532561332642113/185062500000000000000000000000000 : ℝ)*base71 + (304682071507/231328125000000000000000000 : ℝ)*base73 + (3070387367404107887/185062500000000000000000000000000 : ℝ)*base76 + (578724594988857887/185062500000000000000000000000000 : ℝ)*base78 + (616795369343232887/185062500000000000000000000000000 : ℝ)*base80 + (40122974884411/7402500000000000000000000000 : ℝ)*base82 + (67376411/5000000000000000000000 : ℝ)*base90 + (67376411/5000000000000000000000 : ℝ)*base92 + (67376411/5000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181751308649838621604711637/41125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127742433/12500000000000 : ℝ)*(base19) + (130144071/10000000000000 : ℝ)*(base23) + (7441187/5000000000000 : ℝ)*(upper3) + (13203987/20000000000000 : ℝ)*(lower4) + (501727/50000000000000 : ℝ)*(upper5) + (1465645815542337/25000000000000 : ℝ)*(major0) + (1465645815542337/25000000000000 : ℝ)*(major1) + (1465645815542337/25000000000000 : ℝ)*(major2) + (19580824533/100000000000000 : ℝ)*(sp1) + (30926150363/100000000000000 : ℝ)*(sp2) + (7830497131141993/100000000000000 : ℝ)*(sp4) + (1957619132094499/25000000000000 : ℝ)*(sp5) + (195761622588773/2500000000000 : ℝ)*(sp6) + (1947334622940269/50000000000000 : ℝ)*(sp7) + (1947334622940269/50000000000000 : ℝ)*(f.failure) + (7830497131141993/100000000000000 : ℝ)*(f.sum) + (5568054247727/4935000000000000000000000000 : ℝ)*base65 + (593851928703488363/246750000000000000000000000000000 : ℝ)*base67 + (1140518164943738363/246750000000000000000000000000000 : ℝ)*base69 + (507614409552488363/246750000000000000000000000000000 : ℝ)*base71 + (1334074250009/2467500000000000000000000000 : ℝ)*base74 + (1432540471654011637/246750000000000000000000000000000 : ℝ)*base76 + (3934094029804988363/246750000000000000000000000000000 : ℝ)*base77 + (3053032348761261637/246750000000000000000000000000000 : ℝ)*base80 + (3545923804667/4935000000000000000000000000 : ℝ)*base81 + (34800669/5000000000000000000000 : ℝ)*base90 + (34800669/5000000000000000000000 : ℝ)*base92 + (34800669/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1196_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1196_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1196_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1196_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1196_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

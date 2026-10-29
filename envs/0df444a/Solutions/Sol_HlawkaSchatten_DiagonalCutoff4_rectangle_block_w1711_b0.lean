-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1711_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:39.29102+00:00
-- url     : https://prove2.me/submissions/8893957c-cd46-4add-82fa-8ff227ec3ef0

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
theorem support_rectangle_w1711_s0_0 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-333413037/2500000000 : ℝ)*x 0 + (142396353/250000000 : ℝ)*x 1 + (2480629909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333413037/2500000000 : ℝ)^5311 ≤ (8242306710843/100000000000000 : ℝ)^4287 := by
    have hnat : (333413037 : ℕ)^5311*100000000000000^4287 ≤ 8242306710843^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333413037 2500000000 8242306710843 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142396353/250000000 : ℝ)^5311 ≤ (49793337550399/100000000000000 : ℝ)^4287 := by
    have hnat : (142396353 : ℕ)^5311*100000000000000^4287 ≤ 49793337550399^4287*250000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142396353 250000000 49793337550399 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2480629909/5000000000 : ℝ)^5311 ≤ (335714845789/800000000000 : ℝ)^4287 := by
    have hnat : (2480629909 : ℕ)^5311*800000000000^4287 ≤ 335714845789^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480629909 5000000000 335714845789 800000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-333413037/2500000000 : ℝ), (142396353/250000000 : ℝ), (2480629909/5000000000 : ℝ)] ![(8242306710843/100000000000000 : ℝ), (49793337550399/100000000000000 : ℝ), (335714845789/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-333413037/2500000000 : ℝ)|^5311 ≤ (8242306710843/100000000000000 : ℝ)^4287
        have hw : |(-333413037/2500000000 : ℝ)|=(333413037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142396353/250000000 : ℝ)|^5311 ≤ (49793337550399/100000000000000 : ℝ)^4287
        have hw : |(142396353/250000000 : ℝ)|=(142396353/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2480629909/5000000000 : ℝ)|^5311 ≤ (335714845789/800000000000 : ℝ)^4287
        have hw : |(2480629909/5000000000 : ℝ)|=(2480629909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_1 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403577237/10000000000 : ℝ)*x 0 + (-1731303443/10000000000 : ℝ)*x 1 + (4961259549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403577237/10000000000 : ℝ)^5311 ≤ (46647587315571/100000000000000 : ℝ)^4287 := by
    have hnat : (5403577237 : ℕ)^5311*100000000000000^4287 ≤ 46647587315571^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403577237 10000000000 46647587315571 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1731303443/10000000000 : ℝ)^5311 ≤ (11388059771189/100000000000000 : ℝ)^4287 := by
    have hnat : (1731303443 : ℕ)^5311*100000000000000^4287 ≤ 11388059771189^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731303443 10000000000 11388059771189 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4961259549/10000000000 : ℝ)^5311 ≤ (41964352904829/100000000000000 : ℝ)^4287 := by
    have hnat : (4961259549 : ℕ)^5311*100000000000000^4287 ≤ 41964352904829^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4961259549 10000000000 41964352904829 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403577237/10000000000 : ℝ), (-1731303443/10000000000 : ℝ), (4961259549/10000000000 : ℝ)] ![(46647587315571/100000000000000 : ℝ), (11388059771189/100000000000000 : ℝ), (41964352904829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403577237/10000000000 : ℝ)|^5311 ≤ (46647587315571/100000000000000 : ℝ)^4287
        have hw : |(5403577237/10000000000 : ℝ)|=(5403577237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1731303443/10000000000 : ℝ)|^5311 ≤ (11388059771189/100000000000000 : ℝ)^4287
        have hw : |(-1731303443/10000000000 : ℝ)|=(1731303443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4961259549/10000000000 : ℝ)|^5311 ≤ (41964352904829/100000000000000 : ℝ)^4287
        have hw : |(4961259549/10000000000 : ℝ)|=(4961259549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_2 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701788531/5000000000 : ℝ)*x 0 + (99225193/200000000 : ℝ)*x 1 + (-1731303543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701788531/5000000000 : ℝ)^5311 ≤ (4664758544399/10000000000000 : ℝ)^4287 := by
    have hnat : (2701788531 : ℕ)^5311*10000000000000^4287 ≤ 4664758544399^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701788531 5000000000 4664758544399 10000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99225193/200000000 : ℝ)^5311 ≤ (41964353963187/100000000000000 : ℝ)^4287 := by
    have hnat : (99225193 : ℕ)^5311*100000000000000^4287 ≤ 41964353963187^4287*200000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99225193 200000000 41964353963187 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1731303543/10000000000 : ℝ)^5311 ≤ (71175378663/625000000000 : ℝ)^4287 := by
    have hnat : (1731303543 : ℕ)^5311*625000000000^4287 ≤ 71175378663^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731303543 10000000000 71175378663 625000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701788531/5000000000 : ℝ), (99225193/200000000 : ℝ), (-1731303543/10000000000 : ℝ)] ![(4664758544399/10000000000000 : ℝ), (41964353963187/100000000000000 : ℝ), (71175378663/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701788531/5000000000 : ℝ)|^5311 ≤ (4664758544399/10000000000000 : ℝ)^4287
        have hw : |(2701788531/5000000000 : ℝ)|=(2701788531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(99225193/200000000 : ℝ)|^5311 ≤ (41964353963187/100000000000000 : ℝ)^4287
        have hw : |(99225193/200000000 : ℝ)|=(99225193/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1731303543/10000000000 : ℝ)|^5311 ≤ (71175378663/625000000000 : ℝ)^4287
        have hw : |(-1731303543/10000000000 : ℝ)|=(1731303543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_3 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4038731649/10000000000 : ℝ)*x 0 + (3059626173/10000000000 : ℝ)*x 1 + (5194244309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4038731649/10000000000 : ℝ)^5311 ≤ (1300924251313/4000000000000 : ℝ)^4287 := by
    have hnat : (4038731649 : ℕ)^5311*4000000000000^4287 ≤ 1300924251313^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038731649 10000000000 1300924251313 4000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059626173/10000000000 : ℝ)^5311 ≤ (11528804017259/50000000000000 : ℝ)^4287 := by
    have hnat : (3059626173 : ℕ)^5311*50000000000000^4287 ≤ 11528804017259^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059626173 10000000000 11528804017259 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194244309/10000000000 : ℝ)^5311 ≤ (8883857132923/20000000000000 : ℝ)^4287 := by
    have hnat : (5194244309 : ℕ)^5311*20000000000000^4287 ≤ 8883857132923^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194244309 10000000000 8883857132923 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4038731649/10000000000 : ℝ), (3059626173/10000000000 : ℝ), (5194244309/10000000000 : ℝ)] ![(1300924251313/4000000000000 : ℝ), (11528804017259/50000000000000 : ℝ), (8883857132923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4038731649/10000000000 : ℝ)|^5311 ≤ (1300924251313/4000000000000 : ℝ)^4287
        have hw : |(4038731649/10000000000 : ℝ)|=(4038731649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059626173/10000000000 : ℝ)|^5311 ≤ (11528804017259/50000000000000 : ℝ)^4287
        have hw : |(3059626173/10000000000 : ℝ)|=(3059626173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194244309/10000000000 : ℝ)|^5311 ≤ (8883857132923/20000000000000 : ℝ)^4287
        have hw : |(5194244309/10000000000 : ℝ)|=(5194244309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_4 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1335306647/10000000000 : ℝ)*x 0 + (4979291829/10000000000 : ℝ)*x 1 + (5677222449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335306647/10000000000 : ℝ)^5311 ≤ (1650995244357/20000000000000 : ℝ)^4287 := by
    have hnat : (1335306647 : ℕ)^5311*20000000000000^4287 ≤ 1650995244357^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335306647 10000000000 1650995244357 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979291829/10000000000 : ℝ)^5311 ≤ (21076695721353/50000000000000 : ℝ)^4287 := by
    have hnat : (4979291829 : ℕ)^5311*50000000000000^4287 ≤ 21076695721353^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979291829 10000000000 21076695721353 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5677222449/10000000000 : ℝ)^5311 ≤ (24795816159011/50000000000000 : ℝ)^4287 := by
    have hnat : (5677222449 : ℕ)^5311*50000000000000^4287 ≤ 24795816159011^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677222449 10000000000 24795816159011 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1335306647/10000000000 : ℝ), (4979291829/10000000000 : ℝ), (5677222449/10000000000 : ℝ)] ![(1650995244357/20000000000000 : ℝ), (21076695721353/50000000000000 : ℝ), (24795816159011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1335306647/10000000000 : ℝ)|^5311 ≤ (1650995244357/20000000000000 : ℝ)^4287
        have hw : |(-1335306647/10000000000 : ℝ)|=(1335306647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979291829/10000000000 : ℝ)|^5311 ≤ (21076695721353/50000000000000 : ℝ)^4287
        have hw : |(4979291829/10000000000 : ℝ)|=(4979291829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5677222449/10000000000 : ℝ)|^5311 ≤ (24795816159011/50000000000000 : ℝ)^4287
        have hw : |(5677222449/10000000000 : ℝ)|=(5677222449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_5 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040919977/2000000000 : ℝ)*x 0 + (-507670259/5000000000 : ℝ)*x 1 + (5677222051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040919977/2000000000 : ℝ)^5311 ≤ (44529021789227/100000000000000 : ℝ)^4287 := by
    have hnat : (1040919977 : ℕ)^5311*100000000000000^4287 ≤ 44529021789227^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040919977 2000000000 44529021789227 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507670259/5000000000 : ℝ)^5311 ≤ (1469837546683/25000000000000 : ℝ)^4287 := by
    have hnat : (507670259 : ℕ)^5311*25000000000000^4287 ≤ 1469837546683^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507670259 5000000000 1469837546683 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5677222051/10000000000 : ℝ)^5311 ≤ (49591628010987/100000000000000 : ℝ)^4287 := by
    have hnat : (5677222051 : ℕ)^5311*100000000000000^4287 ≤ 49591628010987^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677222051 10000000000 49591628010987 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040919977/2000000000 : ℝ), (-507670259/5000000000 : ℝ), (5677222051/10000000000 : ℝ)] ![(44529021789227/100000000000000 : ℝ), (1469837546683/25000000000000 : ℝ), (49591628010987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040919977/2000000000 : ℝ)|^5311 ≤ (44529021789227/100000000000000 : ℝ)^4287
        have hw : |(1040919977/2000000000 : ℝ)|=(1040919977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507670259/5000000000 : ℝ)|^5311 ≤ (1469837546683/25000000000000 : ℝ)^4287
        have hw : |(-507670259/5000000000 : ℝ)|=(507670259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5677222051/10000000000 : ℝ)|^5311 ≤ (49591628010987/100000000000000 : ℝ)^4287
        have hw : |(5677222051/10000000000 : ℝ)|=(5677222051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_6 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204599647/10000000000 : ℝ)*x 0 + (5677222347/10000000000 : ℝ)*x 1 + (-126917553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204599647/10000000000 : ℝ)^5311 ≤ (8905803853317/20000000000000 : ℝ)^4287 := by
    have hnat : (5204599647 : ℕ)^5311*20000000000000^4287 ≤ 8905803853317^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204599647 10000000000 8905803853317 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5677222347/10000000000 : ℝ)^5311 ≤ (49591631214209/100000000000000 : ℝ)^4287 := by
    have hnat : (5677222347 : ℕ)^5311*100000000000000^4287 ≤ 49591631214209^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677222347 10000000000 49591631214209 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126917553/1250000000 : ℝ)^5311 ≤ (734918689051/12500000000000 : ℝ)^4287 := by
    have hnat : (126917553 : ℕ)^5311*12500000000000^4287 ≤ 734918689051^4287*1250000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126917553 1250000000 734918689051 12500000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204599647/10000000000 : ℝ), (5677222347/10000000000 : ℝ), (-126917553/1250000000 : ℝ)] ![(8905803853317/20000000000000 : ℝ), (49591631214209/100000000000000 : ℝ), (734918689051/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204599647/10000000000 : ℝ)|^5311 ≤ (8905803853317/20000000000000 : ℝ)^4287
        have hw : |(5204599647/10000000000 : ℝ)|=(5204599647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5677222347/10000000000 : ℝ)|^5311 ≤ (49591631214209/100000000000000 : ℝ)^4287
        have hw : |(5677222347/10000000000 : ℝ)|=(5677222347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126917553/1250000000 : ℝ)|^5311 ≤ (734918689051/12500000000000 : ℝ)^4287
        have hw : |(-126917553/1250000000 : ℝ)|=(126917553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s0_7 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2021768211/5000000000 : ℝ)*x 0 + (205673807/400000000 : ℝ)*x 1 + (3113765847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021768211/5000000000 : ℝ)^5311 ≤ (16285523492799/50000000000000 : ℝ)^4287 := by
    have hnat : (2021768211 : ℕ)^5311*50000000000000^4287 ≤ 16285523492799^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021768211 5000000000 16285523492799 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205673807/400000000 : ℝ)^5311 ≤ (43864824387877/100000000000000 : ℝ)^4287 := by
    have hnat : (205673807 : ℕ)^5311*100000000000000^4287 ≤ 43864824387877^4287*400000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205673807 400000000 43864824387877 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3113765847/10000000000 : ℝ)^5311 ≤ (2356412860887/10000000000000 : ℝ)^4287 := by
    have hnat : (3113765847 : ℕ)^5311*10000000000000^4287 ≤ 2356412860887^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3113765847 10000000000 2356412860887 10000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2021768211/5000000000 : ℝ), (205673807/400000000 : ℝ), (3113765847/10000000000 : ℝ)] ![(16285523492799/50000000000000 : ℝ), (43864824387877/100000000000000 : ℝ), (2356412860887/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2021768211/5000000000 : ℝ)|^5311 ≤ (16285523492799/50000000000000 : ℝ)^4287
        have hw : |(2021768211/5000000000 : ℝ)|=(2021768211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205673807/400000000 : ℝ)|^5311 ≤ (43864824387877/100000000000000 : ℝ)^4287
        have hw : |(205673807/400000000 : ℝ)|=(205673807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3113765847/10000000000 : ℝ)|^5311 ≤ (2356412860887/10000000000000 : ℝ)^4287
        have hw : |(3113765847/10000000000 : ℝ)|=(3113765847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1711_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (38/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10937/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5303/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5303 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5303*1^1024 ≤ 0^1024*1^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5303/1024 : ℝ) ≤ (869328113441549483/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5303 ≤ (869328113441549483/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5303*100000000000000000000^1024 ≤ 869328113441549483^1024*5^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 869328113441549483 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (869328113441549483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5303 := by
      have hnat : (1 : ℕ)^1024*1^5303 ≤ 1^5303*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100869328113441549483/100000000000000000000 : ℝ) ≤ (5008364002034551/5000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (100869328113441549483/100000000000000000000 : ℝ)^1024 ≤ (5008364002034551/5000000000000000 : ℝ)^5303 := by
      have hnat : (100869328113441549483 : ℕ)^1024*5000000000000000^5303 ≤ 5008364002034551^5303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100869328113441549483 100000000000000000000 5008364002034551 5000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008364002034551/5000000000000000 : ℝ)) (X := (100869328113441549483/100000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50869328113441549483/50000000000000000000 : ℝ) ≤ (2508364002034551/2500000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50869328113441549483/50000000000000000000 : ℝ)^1024 ≤ (2508364002034551/2500000000000000 : ℝ)^5303 := by
      have hnat : (50869328113441549483 : ℕ)^1024*2500000000000000^5303 ≤ 2508364002034551^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50869328113441549483 50000000000000000000 2508364002034551 2500000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508364002034551/2500000000000000 : ℝ)) (X := (50869328113441549483/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8364002034551/2000000000000000 : ℝ)*(0 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8364002034551/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(869328113441549483/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8364002034551/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5303/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8364002034551/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5008364002034551/5000000000000000 : ℝ) by norm_num, show 1+(869328113441549483/100000000000000000000 : ℝ)+(0 : ℝ)=(100869328113441549483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(869328113441549483/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8364002034551/2000000000000000 : ℝ)*(2/5 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8364002034551/2000000000000000 : ℝ)*(2/5 : ℝ)=(2508364002034551/2500000000000000 : ℝ) by norm_num, show 1+2*(869328113441549483/100000000000000000000 : ℝ)=(50869328113441549483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8364002034551/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8364002034551/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8364002034551/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8364002034551/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8364002034551/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8364002034551/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-333413037/2500000000 : ℝ)*X 0 0+(142396353/250000000 : ℝ)*X 0 1+(2480629909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403577237/10000000000 : ℝ)*X 1 0+(-1731303443/10000000000 : ℝ)*X 1 1+(4961259549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701788531/5000000000 : ℝ)*X 2 0+(99225193/200000000 : ℝ)*X 2 1+(-1731303543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4038731649/10000000000 : ℝ)*X 0 0+(3059626173/10000000000 : ℝ)*X 0 1+(5194244309/10000000000 : ℝ)*X 0 2+(4038731649/10000000000 : ℝ)*X 1 0+(3059626173/10000000000 : ℝ)*X 1 1+(5194244309/10000000000 : ℝ)*X 1 2+(4038731649/10000000000 : ℝ)*X 2 0+(3059626173/10000000000 : ℝ)*X 2 1+(5194244309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1335306647/10000000000 : ℝ)*X 0 0+(4979291829/10000000000 : ℝ)*X 0 1+(5677222449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1040919977/2000000000 : ℝ)*X 1 0+(-507670259/5000000000 : ℝ)*X 1 1+(5677222051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5204599647/10000000000 : ℝ)*X 2 0+(5677222347/10000000000 : ℝ)*X 2 1+(-126917553/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2021768211/5000000000 : ℝ)*X 0 0+(205673807/400000000 : ℝ)*X 0 1+(3113765847/10000000000 : ℝ)*X 0 2+(2021768211/5000000000 : ℝ)*X 1 0+(205673807/400000000 : ℝ)*X 1 1+(3113765847/10000000000 : ℝ)*X 1 2+(2021768211/5000000000 : ℝ)*X 2 0+(205673807/400000000 : ℝ)*X 2 1+(3113765847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70595213703552017659587/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3743469/4000000000000 : ℝ)*(base1) + (634423389/100000000000000 : ℝ)*(base19) + (590336421/100000000000000 : ℝ)*(base23) + (104485813/100000000000000 : ℝ)*(upper3) + (27483789/50000000000000 : ℝ)*(upper5) + (914884536167079/100000000000000 : ℝ)*(major0) + (914884536167079/100000000000000 : ℝ)*(major1) + (914884536167079/100000000000000 : ℝ)*(major2) + (340324481100773/25000000000000 : ℝ)*(sp0) + (1361299041934831/100000000000000 : ℝ)*(sp1) + (6806495430109/500000000000 : ℝ)*(sp2) + (234234219937591/50000000000000 : ℝ)*(sp3) + (461385463/25000000000000 : ℝ)*(sp4) + (744855337/100000000000000 : ℝ)*(sp7) + (468469278317243/100000000000000 : ℝ)*(f.failure) + (68064983817911/5000000000000 : ℝ)*(f.sum) + (91069480453471/100000000000000000000000000000 : ℝ)*base66 + (538671495053471/200000000000000000000000000000 : ℝ)*base68 + (262922229453471/200000000000000000000000000000 : ℝ)*base70 + (635832989053471/200000000000000000000000000000 : ℝ)*base72 + (306787166053471/100000000000000000000000000000 : ℝ)*base74 + (333786087546529/200000000000000000000000000000 : ℝ)*base75 + (1052414919653471/200000000000000000000000000000 : ℝ)*base78 + (840732225453471/200000000000000000000000000000 : ℝ)*base80 + (99788460953471/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (16425489/10000000000000000000000 : ℝ)*base89 + (16425489/10000000000000000000000 : ℝ)*base91 + (16425489/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (205172088366767320028463/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2220431247/100000000000000 : ℝ)*(base19) + (578522327/25000000000000 : ℝ)*(base23) + (9054453/12500000000000 : ℝ)*(upper2) + (340458821/100000000000000 : ℝ)*(upper3) + (21485277/6250000000000 : ℝ)*(upper5) + (962942058370229/100000000000000 : ℝ)*(major0) + (962942058370229/100000000000000 : ℝ)*(major1) + (962942058370229/100000000000000 : ℝ)*(major2) + (3927290879/50000000000000 : ℝ)*(sp1) + (1675554771/20000000000000 : ℝ)*(sp2) + (179100821416641/12500000000000 : ℝ)*(sp4) + (716398248160061/50000000000000 : ℝ)*(sp5) + (286559175893993/20000000000000 : ℝ)*(sp6) + (493077271844541/100000000000000 : ℝ)*(sp7) + (493077271844541/100000000000000 : ℝ)*(f.failure) + (179100821416641/12500000000000 : ℝ)*(f.sum) + (204588159182179/100000000000000000000000000000 : ℝ)*base65 + (47485050382179/200000000000000000000000000000 : ℝ)*base67 + (803518867982179/200000000000000000000000000000 : ℝ)*base69 + (1278355024182179/200000000000000000000000000000 : ℝ)*base71 + (454369160717821/100000000000000000000000000000 : ℝ)*base74 + (2180893489582179/200000000000000000000000000000 : ℝ)*base75 + (414597474382179/200000000000000000000000000000 : ℝ)*base77 + (535015551782179/200000000000000000000000000000 : ℝ)*base79 + (154499427582179/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6758743/10000000000000000000000 : ℝ)*base89 + (6758743/10000000000000000000000 : ℝ)*base91 + (6758743/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1711_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (38/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10937/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1711_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1711_s1_0 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1404920619/10000000000 : ℝ)*x 0 + (1096783713/2000000000 : ℝ)*x 1 + (5126267963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1404920619/10000000000 : ℝ)^5311 ≤ (549463036507/6250000000000 : ℝ)^4287 := by
    have hnat : (1404920619 : ℕ)^5311*6250000000000^4287 ≤ 549463036507^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404920619 10000000000 549463036507 6250000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096783713/2000000000 : ℝ)^5311 ≤ (47508337773757/100000000000000 : ℝ)^4287 := by
    have hnat : (1096783713 : ℕ)^5311*100000000000000^4287 ≤ 47508337773757^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096783713 2000000000 47508337773757 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126267963/10000000000 : ℝ)^5311 ≤ (43700253631957/100000000000000 : ℝ)^4287 := by
    have hnat : (5126267963 : ℕ)^5311*100000000000000^4287 ≤ 43700253631957^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126267963 10000000000 43700253631957 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1404920619/10000000000 : ℝ), (1096783713/2000000000 : ℝ), (5126267963/10000000000 : ℝ)] ![(549463036507/6250000000000 : ℝ), (47508337773757/100000000000000 : ℝ), (43700253631957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1404920619/10000000000 : ℝ)|^5311 ≤ (549463036507/6250000000000 : ℝ)^4287
        have hw : |(-1404920619/10000000000 : ℝ)|=(1404920619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096783713/2000000000 : ℝ)|^5311 ≤ (47508337773757/100000000000000 : ℝ)^4287
        have hw : |(1096783713/2000000000 : ℝ)|=(1096783713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126267963/10000000000 : ℝ)|^5311 ≤ (43700253631957/100000000000000 : ℝ)^4287
        have hw : |(5126267963/10000000000 : ℝ)|=(5126267963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_1 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167097619/312500000 : ℝ)*x 0 + (-1590890759/10000000000 : ℝ)*x 1 + (256313349/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167097619/312500000 : ℝ)^5311 ≤ (46044587338659/100000000000000 : ℝ)^4287 := by
    have hnat : (167097619 : ℕ)^5311*100000000000000^4287 ≤ 46044587338659^4287*312500000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167097619 312500000 46044587338659 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590890759/10000000000 : ℝ)^5311 ≤ (10255169390003/100000000000000 : ℝ)^4287 := by
    have hnat : (1590890759 : ℕ)^5311*100000000000000^4287 ≤ 10255169390003^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590890759 10000000000 10255169390003 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256313349/500000000 : ℝ)^5311 ≤ (10925060812621/25000000000000 : ℝ)^4287 := by
    have hnat : (256313349 : ℕ)^5311*25000000000000^4287 ≤ 10925060812621^4287*500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256313349 500000000 10925060812621 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167097619/312500000 : ℝ), (-1590890759/10000000000 : ℝ), (256313349/500000000 : ℝ)] ![(46044587338659/100000000000000 : ℝ), (10255169390003/100000000000000 : ℝ), (10925060812621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167097619/312500000 : ℝ)|^5311 ≤ (46044587338659/100000000000000 : ℝ)^4287
        have hw : |(167097619/312500000 : ℝ)|=(167097619/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590890759/10000000000 : ℝ)|^5311 ≤ (10255169390003/100000000000000 : ℝ)^4287
        have hw : |(-1590890759/10000000000 : ℝ)|=(1590890759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256313349/500000000 : ℝ)|^5311 ≤ (10925060812621/25000000000000 : ℝ)^4287
        have hw : |(256313349/500000000 : ℝ)|=(256313349/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_2 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347122423/10000000000 : ℝ)*x 0 + (2563134083/5000000000 : ℝ)*x 1 + (-1590891041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347122423/10000000000 : ℝ)^5311 ≤ (23022286281771/50000000000000 : ℝ)^4287 := by
    have hnat : (5347122423 : ℕ)^5311*50000000000000^4287 ≤ 23022286281771^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347122423 10000000000 23022286281771 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563134083/5000000000 : ℝ)^5311 ≤ (21850127887921/50000000000000 : ℝ)^4287 := by
    have hnat : (2563134083 : ℕ)^5311*50000000000000^4287 ≤ 21850127887921^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563134083 5000000000 21850127887921 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1590891041/10000000000 : ℝ)^5311 ≤ (5127585821017/50000000000000 : ℝ)^4287 := by
    have hnat : (1590891041 : ℕ)^5311*50000000000000^4287 ≤ 5127585821017^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590891041 10000000000 5127585821017 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347122423/10000000000 : ℝ), (2563134083/5000000000 : ℝ), (-1590891041/10000000000 : ℝ)] ![(23022286281771/50000000000000 : ℝ), (21850127887921/50000000000000 : ℝ), (5127585821017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347122423/10000000000 : ℝ)|^5311 ≤ (23022286281771/50000000000000 : ℝ)^4287
        have hw : |(5347122423/10000000000 : ℝ)|=(5347122423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563134083/5000000000 : ℝ)|^5311 ≤ (21850127887921/50000000000000 : ℝ)^4287
        have hw : |(2563134083/5000000000 : ℝ)|=(2563134083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1590891041/10000000000 : ℝ)|^5311 ≤ (5127585821017/50000000000000 : ℝ)^4287
        have hw : |(-1590891041/10000000000 : ℝ)|=(1590891041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_3 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (256292741/625000000 : ℝ)*x 0 + (3601805651/10000000000 : ℝ)*x 1 + (36258451/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256292741/625000000 : ℝ)^5311 ≤ (4142786059039/12500000000000 : ℝ)^4287 := by
    have hnat : (256292741 : ℕ)^5311*12500000000000^4287 ≤ 4142786059039^4287*625000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256292741 625000000 4142786059039 12500000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3601805651/10000000000 : ℝ)^5311 ≤ (28222141518689/100000000000000 : ℝ)^4287 := by
    have hnat : (3601805651 : ℕ)^5311*100000000000000^4287 ≤ 28222141518689^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3601805651 10000000000 28222141518689 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36258451/78125000 : ℝ)^5311 ≤ (38635570003479/100000000000000 : ℝ)^4287 := by
    have hnat : (36258451 : ℕ)^5311*100000000000000^4287 ≤ 38635570003479^4287*78125000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36258451 78125000 38635570003479 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256292741/625000000 : ℝ), (3601805651/10000000000 : ℝ), (36258451/78125000 : ℝ)] ![(4142786059039/12500000000000 : ℝ), (28222141518689/100000000000000 : ℝ), (38635570003479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256292741/625000000 : ℝ)|^5311 ≤ (4142786059039/12500000000000 : ℝ)^4287
        have hw : |(256292741/625000000 : ℝ)|=(256292741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3601805651/10000000000 : ℝ)|^5311 ≤ (28222141518689/100000000000000 : ℝ)^4287
        have hw : |(3601805651/10000000000 : ℝ)|=(3601805651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36258451/78125000 : ℝ)|^5311 ≤ (38635570003479/100000000000000 : ℝ)^4287
        have hw : |(36258451/78125000 : ℝ)|=(36258451/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_4 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1405110929/10000000000 : ℝ)*x 0 + (5130548261/10000000000 : ℝ)*x 1 + (342473023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1405110929/10000000000 : ℝ)^5311 ≤ (4396441972271/50000000000000 : ℝ)^4287 := by
    have hnat : (1405110929 : ℕ)^5311*50000000000000^4287 ≤ 4396441972271^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405110929 10000000000 4396441972271 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130548261/10000000000 : ℝ)^5311 ≤ (874909248213/2000000000000 : ℝ)^4287 := by
    have hnat : (5130548261 : ℕ)^5311*2000000000000^4287 ≤ 874909248213^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130548261 10000000000 874909248213 2000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342473023/625000000 : ℝ)^5311 ≤ (47461653627001/100000000000000 : ℝ)^4287 := by
    have hnat : (342473023 : ℕ)^5311*100000000000000^4287 ≤ 47461653627001^4287*625000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342473023 625000000 47461653627001 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1405110929/10000000000 : ℝ), (5130548261/10000000000 : ℝ), (342473023/625000000 : ℝ)] ![(4396441972271/50000000000000 : ℝ), (874909248213/2000000000000 : ℝ), (47461653627001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1405110929/10000000000 : ℝ)|^5311 ≤ (4396441972271/50000000000000 : ℝ)^4287
        have hw : |(-1405110929/10000000000 : ℝ)|=(1405110929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130548261/10000000000 : ℝ)|^5311 ≤ (874909248213/2000000000000 : ℝ)^4287
        have hw : |(5130548261/10000000000 : ℝ)|=(5130548261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342473023/625000000 : ℝ)|^5311 ≤ (47461653627001/100000000000000 : ℝ)^4287
        have hw : |(342473023/625000000 : ℝ)|=(342473023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_5 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251352203/10000000000 : ℝ)*x 0 + (-1237589777/10000000000 : ℝ)*x 1 + (5479568063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251352203/10000000000 : ℝ)^5311 ≤ (22512547852781/50000000000000 : ℝ)^4287 := by
    have hnat : (5251352203 : ℕ)^5311*50000000000000^4287 ≤ 22512547852781^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251352203 10000000000 22512547852781 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1237589777/10000000000 : ℝ)^5311 ≤ (7513253930019/100000000000000 : ℝ)^4287 := by
    have hnat : (1237589777 : ℕ)^5311*100000000000000^4287 ≤ 7513253930019^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237589777 10000000000 7513253930019 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479568063/10000000000 : ℝ)^5311 ≤ (47461650354203/100000000000000 : ℝ)^4287 := by
    have hnat : (5479568063 : ℕ)^5311*100000000000000^4287 ≤ 47461650354203^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479568063 10000000000 47461650354203 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251352203/10000000000 : ℝ), (-1237589777/10000000000 : ℝ), (5479568063/10000000000 : ℝ)] ![(22512547852781/50000000000000 : ℝ), (7513253930019/100000000000000 : ℝ), (47461650354203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251352203/10000000000 : ℝ)|^5311 ≤ (22512547852781/50000000000000 : ℝ)^4287
        have hw : |(5251352203/10000000000 : ℝ)|=(5251352203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1237589777/10000000000 : ℝ)|^5311 ≤ (7513253930019/100000000000000 : ℝ)^4287
        have hw : |(-1237589777/10000000000 : ℝ)|=(1237589777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479568063/10000000000 : ℝ)|^5311 ≤ (47461650354203/100000000000000 : ℝ)^4287
        have hw : |(5479568063/10000000000 : ℝ)|=(5479568063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_6 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251352349/10000000000 : ℝ)*x 0 + (5479567737/10000000000 : ℝ)*x 1 + (-247518007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251352349/10000000000 : ℝ)^5311 ≤ (22512548628187/50000000000000 : ℝ)^4287 := by
    have hnat : (5251352349 : ℕ)^5311*50000000000000^4287 ≤ 22512548628187^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251352349 10000000000 22512548628187 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479567737/10000000000 : ℝ)^5311 ≤ (9492329371213/20000000000000 : ℝ)^4287 := by
    have hnat : (5479567737 : ℕ)^5311*20000000000000^4287 ≤ 9492329371213^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479567737 10000000000 9492329371213 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247518007/2000000000 : ℝ)^5311 ≤ (7513255870431/100000000000000 : ℝ)^4287 := by
    have hnat : (247518007 : ℕ)^5311*100000000000000^4287 ≤ 7513255870431^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247518007 2000000000 7513255870431 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251352349/10000000000 : ℝ), (5479567737/10000000000 : ℝ), (-247518007/2000000000 : ℝ)] ![(22512548628187/50000000000000 : ℝ), (9492329371213/20000000000000 : ℝ), (7513255870431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251352349/10000000000 : ℝ)|^5311 ≤ (22512548628187/50000000000000 : ℝ)^4287
        have hw : |(5251352349/10000000000 : ℝ)|=(5251352349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479567737/10000000000 : ℝ)|^5311 ≤ (9492329371213/20000000000000 : ℝ)^4287
        have hw : |(5479567737/10000000000 : ℝ)|=(5479567737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247518007/2000000000 : ℝ)|^5311 ≤ (7513255870431/100000000000000 : ℝ)^4287
        have hw : |(-247518007/2000000000 : ℝ)|=(247518007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s1_7 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4101233933/10000000000 : ℝ)*x 0 + (4628642583/10000000000 : ℝ)*x 1 + (361444439/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4101233933/10000000000 : ℝ)^5311 ≤ (33147796288859/100000000000000 : ℝ)^4287 := by
    have hnat : (4101233933 : ℕ)^5311*100000000000000^4287 ≤ 33147796288859^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101233933 10000000000 33147796288859 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4628642583/10000000000 : ℝ)^5311 ≤ (9626831112177/25000000000000 : ℝ)^4287 := by
    have hnat : (4628642583 : ℕ)^5311*25000000000000^4287 ≤ 9626831112177^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4628642583 10000000000 9626831112177 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361444439/1000000000 : ℝ)^5311 ≤ (14172439620411/50000000000000 : ℝ)^4287 := by
    have hnat : (361444439 : ℕ)^5311*50000000000000^4287 ≤ 14172439620411^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361444439 1000000000 14172439620411 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4101233933/10000000000 : ℝ), (4628642583/10000000000 : ℝ), (361444439/1000000000 : ℝ)] ![(33147796288859/100000000000000 : ℝ), (9626831112177/25000000000000 : ℝ), (14172439620411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4101233933/10000000000 : ℝ)|^5311 ≤ (33147796288859/100000000000000 : ℝ)^4287
        have hw : |(4101233933/10000000000 : ℝ)|=(4101233933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4628642583/10000000000 : ℝ)|^5311 ≤ (9626831112177/25000000000000 : ℝ)^4287
        have hw : |(4628642583/10000000000 : ℝ)|=(4628642583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361444439/1000000000 : ℝ)|^5311 ≤ (14172439620411/50000000000000 : ℝ)^4287
        have hw : |(361444439/1000000000 : ℝ)|=(361444439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1711_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (38/625 : ℝ)*pair X i i ≤ pair X i h) :
    (4877/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17391/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10937/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (38/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10937/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (38/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10937/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (38/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10937/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (38/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10937/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (38/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10937/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (38/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (38/625 : ℝ) ^ (5303/1024 : ℝ) ≤ (50371880562279/100000000000000000000 : ℝ) := by
    have hpowers : (38/625 : ℝ)^5303 ≤ (50371880562279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (38 : ℕ)^5303*100000000000000000000^1024 ≤ 50371880562279^1024*625^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38 625 50371880562279 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38/625 : ℝ)) (X := (50371880562279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10937/50000 : ℝ) ^ (5303/1024 : ℝ) ≤ (38166206003537567/100000000000000000000 : ℝ) := by
    have hpowers : (10937/50000 : ℝ)^5303 ≤ (38166206003537567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10937 : ℕ)^5303*100000000000000000000^1024 ≤ 38166206003537567^1024*50000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10937 50000 38166206003537567 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10937/50000 : ℝ)) (X := (38166206003537567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000050371880562279/50000000000000000000 : ℝ) ≤ (10000001945343569/10000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50000050371880562279/50000000000000000000 : ℝ)^1024 ≤ (10000001945343569/10000000000000000 : ℝ)^5303 := by
      have hnat : (50000050371880562279 : ℕ)^1024*10000000000000000^5303 ≤ 10000001945343569^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000050371880562279 50000000000000000000 10000001945343569 10000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001945343569/10000000000000000 : ℝ)) (X := (50000050371880562279/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019108288942049923/50000000000000000000 : ℝ) ≤ (156261528775957/156250000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50019108288942049923/50000000000000000000 : ℝ)^1024 ≤ (156261528775957/156250000000000 : ℝ)^5303 := by
      have hnat : (50019108288942049923 : ℕ)^1024*156250000000000^5303 ≤ 156261528775957^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019108288942049923 50000000000000000000 156261528775957 156250000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156261528775957/156250000000000 : ℝ)) (X := (50019108288942049923/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038166206003537567/50000000000000000000 : ℝ) ≤ (10001473737978927/10000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50038166206003537567/50000000000000000000 : ℝ)^1024 ≤ (10001473737978927/10000000000000000 : ℝ)^5303 := by
      have hnat : (50038166206003537567 : ℕ)^1024*10000000000000000^5303 ≤ 10001473737978927^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038166206003537567 50000000000000000000 10001473737978927 10000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001473737978927/10000000000000000 : ℝ)) (X := (50038166206003537567/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50371880562279/100000000000000000000 : ℝ) ≤ ((78965541112766676073/78970000000000000000 : ℝ)+2*(735896317679/1579400000000000 : ℝ)*(38/625 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (78965541112766676073/78970000000000000000 : ℝ)+2*(735896317679/1579400000000000 : ℝ)*(38/625 : ℝ)=(10000001945343569/10000000000000000 : ℝ) by norm_num, show 1+2*(50371880562279/100000000000000000000 : ℝ)=(50000050371880562279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38166206003537567/100000000000000000000 : ℝ)+(50371880562279/100000000000000000000 : ℝ) ≤ ((78965541112766676073/78970000000000000000 : ℝ)+(735896317679/1579400000000000 : ℝ)*((10937/50000 : ℝ)+(38/625 : ℝ)))^(5303/1024 : ℝ) := by
    rw [show (78965541112766676073/78970000000000000000 : ℝ)+(735896317679/1579400000000000 : ℝ)*((10937/50000 : ℝ)+(38/625 : ℝ))=(156261528775957/156250000000000 : ℝ) by norm_num, show 1+(38166206003537567/100000000000000000000 : ℝ)+(50371880562279/100000000000000000000 : ℝ)=(50019108288942049923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38166206003537567/100000000000000000000 : ℝ) ≤ ((78965541112766676073/78970000000000000000 : ℝ)+2*(735896317679/1579400000000000 : ℝ)*(10937/50000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (78965541112766676073/78970000000000000000 : ℝ)+2*(735896317679/1579400000000000 : ℝ)*(10937/50000 : ℝ)=(10001473737978927/10000000000000000 : ℝ) by norm_num, show 1+2*(38166206003537567/100000000000000000000 : ℝ)=(50038166206003537567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (78965541112766676073/78970000000000000000 : ℝ)*(X 1 0+X 2 0)+(735896317679/1579400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (38/625 : ℝ)) (hi := (10937/50000 : ℝ)) (c := (78965541112766676073/78970000000000000000 : ℝ)) (alpha := (735896317679/1579400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (78965541112766676073/78970000000000000000 : ℝ)*(X 0 1+X 2 1)+(735896317679/1579400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (38/625 : ℝ)) (hi := (10937/50000 : ℝ)) (c := (78965541112766676073/78970000000000000000 : ℝ)) (alpha := (735896317679/1579400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (78965541112766676073/78970000000000000000 : ℝ)*(X 0 2+X 1 2)+(735896317679/1579400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (38/625 : ℝ)) (hi := (10937/50000 : ℝ)) (c := (78965541112766676073/78970000000000000000 : ℝ)) (alpha := (735896317679/1579400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1404920619/10000000000 : ℝ)*X 0 0+(1096783713/2000000000 : ℝ)*X 0 1+(5126267963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167097619/312500000 : ℝ)*X 1 0+(-1590890759/10000000000 : ℝ)*X 1 1+(256313349/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347122423/10000000000 : ℝ)*X 2 0+(2563134083/5000000000 : ℝ)*X 2 1+(-1590891041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((256292741/625000000 : ℝ)*X 0 0+(3601805651/10000000000 : ℝ)*X 0 1+(36258451/78125000 : ℝ)*X 0 2+(256292741/625000000 : ℝ)*X 1 0+(3601805651/10000000000 : ℝ)*X 1 1+(36258451/78125000 : ℝ)*X 1 2+(256292741/625000000 : ℝ)*X 2 0+(3601805651/10000000000 : ℝ)*X 2 1+(36258451/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1405110929/10000000000 : ℝ)*X 0 0+(5130548261/10000000000 : ℝ)*X 0 1+(342473023/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251352203/10000000000 : ℝ)*X 1 0+(-1237589777/10000000000 : ℝ)*X 1 1+(5479568063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251352349/10000000000 : ℝ)*X 2 0+(5479567737/10000000000 : ℝ)*X 2 1+(-247518007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4101233933/10000000000 : ℝ)*X 0 0+(4628642583/10000000000 : ℝ)*X 0 1+(361444439/1000000000 : ℝ)*X 0 2+(4101233933/10000000000 : ℝ)*X 1 0+(4628642583/10000000000 : ℝ)*X 1 1+(361444439/1000000000 : ℝ)*X 1 2+(4101233933/10000000000 : ℝ)*X 2 0+(4628642583/10000000000 : ℝ)*X 2 1+(361444439/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27349206583911195471651/4935625000000000000000000000 : ℝ) := by norm_num
    linear_combination (50999143/50000000000000 : ℝ)*(base19) + (64136777/100000000000000 : ℝ)*(upper2) + (24191531/10000000000000 : ℝ)*(lower4) + (41096809/100000000000000 : ℝ)*(lower5) + (939560838503683/50000000000000 : ℝ)*(major0) + (939560838503683/50000000000000 : ℝ)*(major1) + (939560838503683/50000000000000 : ℝ)*(major2) + (2796032326918463/100000000000000 : ℝ)*(sp0) + (139801292624327/5000000000000 : ℝ)*(sp1) + (139801436899507/5000000000000 : ℝ)*(sp2) + (962209700894063/100000000000000 : ℝ)*(sp3) + (228299213/20000000000000 : ℝ)*(sp4) + (3756964851/50000000000000 : ℝ)*(sp5) + (4730424387/100000000000000 : ℝ)*(sp6) + (962209700894063/100000000000000 : ℝ)*(f.failure) + (43688022943977/1562500000000 : ℝ)*(f.sum) + (128473128396053/39485000000000000000000000000 : ℝ)*base66 + (24270410288024173141/3948500000000000000000000000000000 : ℝ)*base68 + (21105865536404173141/3948500000000000000000000000000000 : ℝ)*base70 + (28857446628702673141/3948500000000000000000000000000000 : ℝ)*base72 + (39521831726629/19742500000000000000000000000 : ℝ)*base74 + (1628872372901326859/3948500000000000000000000000000000 : ℝ)*base75 + (17861732665832826859/3948500000000000000000000000000000 : ℝ)*base77 + (2910957501274326859/3948500000000000000000000000000000 : ℝ)*base79 + (47269812967529/19742500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (140178349/10000000000000000000000 : ℝ)*base89 + (140178349/10000000000000000000000 : ℝ)*base91 + (140178349/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11335990230708227520752991603/1974250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1407491597/100000000000000 : ℝ)*(base19) + (833278893/50000000000000 : ℝ)*(base23) + (53428529/50000000000000 : ℝ)*(upper2) + (18064437/10000000000000 : ℝ)*(upper3) + (246880057/100000000000000 : ℝ)*(upper5) + (1925582241472463/100000000000000 : ℝ)*(major0) + (1925582241472463/100000000000000 : ℝ)*(major1) + (1925582241472463/100000000000000 : ℝ)*(major2) + (10422133763/100000000000000 : ℝ)*(sp1) + (910209127/10000000000000 : ℝ)*(sp2) + (358145540495539/12500000000000 : ℝ)*(sp4) + (2865152494338951/100000000000000 : ℝ)*(sp5) + (573030711063051/20000000000000 : ℝ)*(sp6) + (123249995947899/12500000000000 : ℝ)*(sp7) + (123249995947899/12500000000000 : ℝ)*(f.failure) + (358145540495539/12500000000000 : ℝ)*(f.sum) + (220928214470017/78970000000000000000000000000 : ℝ)*base65 + (24580469697756672201/7897000000000000000000000000000000 : ℝ)*base68 + (39699141359027327799/7897000000000000000000000000000000 : ℝ)*base69 + (80808025183718327799/7897000000000000000000000000000000 : ℝ)*base71 + (387415332947863/78970000000000000000000000000 : ℝ)*base74 + (69624942601238327799/7897000000000000000000000000000000 : ℝ)*base75 + (63996554792462327799/7897000000000000000000000000000000 : ℝ)*base77 + (85726584782512327799/7897000000000000000000000000000000 : ℝ)*base79 + (389117841564927/78970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4820623/1250000000000000000000 : ℝ)*base90 + (4820623/1250000000000000000000 : ℝ)*base92 + (4820623/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1711_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (38/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4877/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17391/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1711_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1711_s2_0 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-352084531/2500000000 : ℝ)*x 0 + (218796053/400000000 : ℝ)*x 1 + (5137995947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352084531/2500000000 : ℝ)^5311 ≤ (4408954867329/50000000000000 : ℝ)^4287 := by
    have hnat : (352084531 : ℕ)^5311*50000000000000^4287 ≤ 4408954867329^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352084531 2500000000 4408954867329 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218796053/400000000 : ℝ)^5311 ≤ (47357943437561/100000000000000 : ℝ)^4287 := by
    have hnat : (218796053 : ℕ)^5311*100000000000000^4287 ≤ 47357943437561^4287*400000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218796053 400000000 47357943437561 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137995947/10000000000 : ℝ)^5311 ≤ (1095603670413/2500000000000 : ℝ)^4287 := by
    have hnat : (5137995947 : ℕ)^5311*2500000000000^4287 ≤ 1095603670413^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137995947 10000000000 1095603670413 2500000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352084531/2500000000 : ℝ), (218796053/400000000 : ℝ), (5137995947/10000000000 : ℝ)] ![(4408954867329/50000000000000 : ℝ), (47357943437561/100000000000000 : ℝ), (1095603670413/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352084531/2500000000 : ℝ)|^5311 ≤ (4408954867329/50000000000000 : ℝ)^4287
        have hw : |(-352084531/2500000000 : ℝ)|=(352084531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218796053/400000000 : ℝ)|^5311 ≤ (47357943437561/100000000000000 : ℝ)^4287
        have hw : |(218796053/400000000 : ℝ)|=(218796053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137995947/10000000000 : ℝ)|^5311 ≤ (1095603670413/2500000000000 : ℝ)^4287
        have hw : |(5137995947/10000000000 : ℝ)|=(5137995947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_1 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343323321/10000000000 : ℝ)*x 0 + (-1580443703/10000000000 : ℝ)*x 1 + (205519839/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343323321/10000000000 : ℝ)^5311 ≤ (4600404735767/10000000000000 : ℝ)^4287 := by
    have hnat : (5343323321 : ℕ)^5311*10000000000000^4287 ≤ 4600404735767^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343323321 10000000000 4600404735767 10000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580443703/10000000000 : ℝ)^5311 ≤ (101718055121/1000000000000 : ℝ)^4287 := by
    have hnat : (1580443703 : ℕ)^5311*1000000000000^4287 ≤ 101718055121^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580443703 10000000000 101718055121 1000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205519839/400000000 : ℝ)^5311 ≤ (4382414711239/10000000000000 : ℝ)^4287 := by
    have hnat : (205519839 : ℕ)^5311*10000000000000^4287 ≤ 4382414711239^4287*400000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205519839 400000000 4382414711239 10000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343323321/10000000000 : ℝ), (-1580443703/10000000000 : ℝ), (205519839/400000000 : ℝ)] ![(4600404735767/10000000000000 : ℝ), (101718055121/1000000000000 : ℝ), (4382414711239/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343323321/10000000000 : ℝ)|^5311 ≤ (4600404735767/10000000000000 : ℝ)^4287
        have hw : |(5343323321/10000000000 : ℝ)|=(5343323321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580443703/10000000000 : ℝ)|^5311 ≤ (101718055121/1000000000000 : ℝ)^4287
        have hw : |(-1580443703/10000000000 : ℝ)|=(1580443703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205519839/400000000 : ℝ)|^5311 ≤ (4382414711239/10000000000000 : ℝ)^4287
        have hw : |(205519839/400000000 : ℝ)|=(205519839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_2 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33395773/62500000 : ℝ)*x 0 + (1284498983/2500000000 : ℝ)*x 1 + (-1580443281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33395773/62500000 : ℝ)^5311 ≤ (359406649897/781250000000 : ℝ)^4287 := by
    have hnat : (33395773 : ℕ)^5311*781250000000^4287 ≤ 359406649897^4287*62500000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33395773 62500000 359406649897 781250000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284498983/2500000000 : ℝ)^5311 ≤ (43824146658019/100000000000000 : ℝ)^4287 := by
    have hnat : (1284498983 : ℕ)^5311*100000000000000^4287 ≤ 43824146658019^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284498983 2500000000 43824146658019 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580443281/10000000000 : ℝ)^5311 ≤ (5085901073669/50000000000000 : ℝ)^4287 := by
    have hnat : (1580443281 : ℕ)^5311*50000000000000^4287 ≤ 5085901073669^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580443281 10000000000 5085901073669 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33395773/62500000 : ℝ), (1284498983/2500000000 : ℝ), (-1580443281/10000000000 : ℝ)] ![(359406649897/781250000000 : ℝ), (43824146658019/100000000000000 : ℝ), (5085901073669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33395773/62500000 : ℝ)|^5311 ≤ (359406649897/781250000000 : ℝ)^4287
        have hw : |(33395773/62500000 : ℝ)|=(33395773/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284498983/2500000000 : ℝ)|^5311 ≤ (43824146658019/100000000000000 : ℝ)^4287
        have hw : |(1284498983/2500000000 : ℝ)|=(1284498983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1580443281/10000000000 : ℝ)|^5311 ≤ (5085901073669/50000000000000 : ℝ)^4287
        have hw : |(-1580443281/10000000000 : ℝ)|=(1580443281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_3 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2051666181/5000000000 : ℝ)*x 0 + (909744453/2500000000 : ℝ)*x 1 + (71928791/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051666181/5000000000 : ℝ)^5311 ≤ (16584404540177/50000000000000 : ℝ)^4287 := by
    have hnat : (2051666181 : ℕ)^5311*50000000000000^4287 ≤ 16584404540177^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051666181 5000000000 16584404540177 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909744453/2500000000 : ℝ)^5311 ≤ (28583421498247/100000000000000 : ℝ)^4287 := by
    have hnat : (909744453 : ℕ)^5311*100000000000000^4287 ≤ 28583421498247^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909744453 2500000000 28583421498247 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71928791/156250000 : ℝ)^5311 ≤ (9561942350407/25000000000000 : ℝ)^4287 := by
    have hnat : (71928791 : ℕ)^5311*25000000000000^4287 ≤ 9561942350407^4287*156250000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71928791 156250000 9561942350407 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2051666181/5000000000 : ℝ), (909744453/2500000000 : ℝ), (71928791/156250000 : ℝ)] ![(16584404540177/50000000000000 : ℝ), (28583421498247/100000000000000 : ℝ), (9561942350407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2051666181/5000000000 : ℝ)|^5311 ≤ (16584404540177/50000000000000 : ℝ)^4287
        have hw : |(2051666181/5000000000 : ℝ)|=(2051666181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(909744453/2500000000 : ℝ)|^5311 ≤ (28583421498247/100000000000000 : ℝ)^4287
        have hw : |(909744453/2500000000 : ℝ)|=(909744453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71928791/156250000 : ℝ)|^5311 ≤ (9561942350407/25000000000000 : ℝ)^4287
        have hw : |(71928791/156250000 : ℝ)|=(71928791/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_4 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22007651/156250000 : ℝ)*x 0 + (2570842551/5000000000 : ℝ)*x 1 + (546615671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22007651/156250000 : ℝ)^5311 ≤ (4409542606179/50000000000000 : ℝ)^4287 := by
    have hnat : (22007651 : ℕ)^5311*50000000000000^4287 ≤ 4409542606179^4287*156250000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22007651 156250000 4409542606179 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570842551/5000000000 : ℝ)^5311 ≤ (21931566317961/50000000000000 : ℝ)^4287 := by
    have hnat : (2570842551 : ℕ)^5311*50000000000000^4287 ≤ 21931566317961^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570842551 5000000000 21931566317961 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546615671/1000000000 : ℝ)^5311 ≤ (23658891066233/50000000000000 : ℝ)^4287 := by
    have hnat : (546615671 : ℕ)^5311*50000000000000^4287 ≤ 23658891066233^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546615671 1000000000 23658891066233 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22007651/156250000 : ℝ), (2570842551/5000000000 : ℝ), (546615671/1000000000 : ℝ)] ![(4409542606179/50000000000000 : ℝ), (21931566317961/50000000000000 : ℝ), (23658891066233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22007651/156250000 : ℝ)|^5311 ≤ (4409542606179/50000000000000 : ℝ)^4287
        have hw : |(-22007651/156250000 : ℝ)|=(22007651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570842551/5000000000 : ℝ)|^5311 ≤ (21931566317961/50000000000000 : ℝ)^4287
        have hw : |(2570842551/5000000000 : ℝ)|=(2570842551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546615671/1000000000 : ℝ)|^5311 ≤ (23658891066233/50000000000000 : ℝ)^4287
        have hw : |(546615671/1000000000 : ℝ)|=(546615671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_5 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627239179/5000000000 : ℝ)*x 0 + (-1252282539/10000000000 : ℝ)*x 1 + (1366539171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627239179/5000000000 : ℝ)^5311 ≤ (22529152042951/50000000000000 : ℝ)^4287 := by
    have hnat : (2627239179 : ℕ)^5311*50000000000000^4287 ≤ 22529152042951^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627239179 5000000000 22529152042951 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252282539/10000000000 : ℝ)^5311 ≤ (1524782809129/20000000000000 : ℝ)^4287 := by
    have hnat : (1252282539 : ℕ)^5311*20000000000000^4287 ≤ 1524782809129^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252282539 10000000000 1524782809129 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366539171/2500000000 : ℝ)^5311 ≤ (47317781853637/100000000000000 : ℝ)^4287 := by
    have hnat : (1366539171 : ℕ)^5311*100000000000000^4287 ≤ 47317781853637^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366539171 2500000000 47317781853637 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627239179/5000000000 : ℝ), (-1252282539/10000000000 : ℝ), (1366539171/2500000000 : ℝ)] ![(22529152042951/50000000000000 : ℝ), (1524782809129/20000000000000 : ℝ), (47317781853637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627239179/5000000000 : ℝ)|^5311 ≤ (22529152042951/50000000000000 : ℝ)^4287
        have hw : |(2627239179/5000000000 : ℝ)|=(2627239179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252282539/10000000000 : ℝ)|^5311 ≤ (1524782809129/20000000000000 : ℝ)^4287
        have hw : |(-1252282539/10000000000 : ℝ)|=(1252282539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366539171/2500000000 : ℝ)|^5311 ≤ (47317781853637/100000000000000 : ℝ)^4287
        have hw : |(1366539171/2500000000 : ℝ)|=(1366539171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_6 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627239157/5000000000 : ℝ)*x 0 + (2733078349/5000000000 : ℝ)*x 1 + (-62614129/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627239157/5000000000 : ℝ)^5311 ≤ (11264575904617/25000000000000 : ℝ)^4287 := by
    have hnat : (2627239157 : ℕ)^5311*25000000000000^4287 ≤ 11264575904617^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627239157 5000000000 11264575904617 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733078349/5000000000 : ℝ)^5311 ≤ (739340343809/1562500000000 : ℝ)^4287 := by
    have hnat : (2733078349 : ℕ)^5311*1562500000000^4287 ≤ 739340343809^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733078349 5000000000 739340343809 1562500000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62614129/500000000 : ℝ)^5311 ≤ (60991314839/800000000000 : ℝ)^4287 := by
    have hnat : (62614129 : ℕ)^5311*800000000000^4287 ≤ 60991314839^4287*500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62614129 500000000 60991314839 800000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627239157/5000000000 : ℝ), (2733078349/5000000000 : ℝ), (-62614129/500000000 : ℝ)] ![(11264575904617/25000000000000 : ℝ), (739340343809/1562500000000 : ℝ), (60991314839/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627239157/5000000000 : ℝ)|^5311 ≤ (11264575904617/25000000000000 : ℝ)^4287
        have hw : |(2627239157/5000000000 : ℝ)|=(2627239157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733078349/5000000000 : ℝ)|^5311 ≤ (739340343809/1562500000000 : ℝ)^4287
        have hw : |(2733078349/5000000000 : ℝ)|=(2733078349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62614129/500000000 : ℝ)|^5311 ≤ (60991314839/800000000000 : ℝ)^4287
        have hw : |(-62614129/500000000 : ℝ)|=(62614129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s2_7 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4103771887/10000000000 : ℝ)*x 0 + (71761287/156250000 : ℝ)*x 1 + (912464487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103771887/10000000000 : ℝ)^5311 ≤ (16586605312641/50000000000000 : ℝ)^4287 := by
    have hnat : (4103771887 : ℕ)^5311*50000000000000^4287 ≤ 16586605312641^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103771887 10000000000 16586605312641 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71761287/156250000 : ℝ)^5311 ≤ (1191795482543/3125000000000 : ℝ)^4287 := by
    have hnat : (71761287 : ℕ)^5311*3125000000000^4287 ≤ 1191795482543^4287*156250000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71761287 156250000 1191795482543 3125000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912464487/2500000000 : ℝ)^5311 ≤ (7172333479037/25000000000000 : ℝ)^4287 := by
    have hnat : (912464487 : ℕ)^5311*25000000000000^4287 ≤ 7172333479037^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912464487 2500000000 7172333479037 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103771887/10000000000 : ℝ), (71761287/156250000 : ℝ), (912464487/2500000000 : ℝ)] ![(16586605312641/50000000000000 : ℝ), (1191795482543/3125000000000 : ℝ), (7172333479037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103771887/10000000000 : ℝ)|^5311 ≤ (16586605312641/50000000000000 : ℝ)^4287
        have hw : |(4103771887/10000000000 : ℝ)|=(4103771887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71761287/156250000 : ℝ)|^5311 ≤ (1191795482543/3125000000000 : ℝ)^4287
        have hw : |(71761287/156250000 : ℝ)|=(71761287/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(912464487/2500000000 : ℝ)|^5311 ≤ (7172333479037/25000000000000 : ℝ)^4287
        have hw : |(912464487/2500000000 : ℝ)|=(912464487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1711_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17391/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4877/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10009/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17391/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4877/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17391/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4877/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17391/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4877/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17391/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4877/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17391/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4877/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17391/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4877/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4877/50000 : ℝ) ^ (5303/1024 : ℝ) ≤ (145616191037523/25000000000000000000 : ℝ) := by
    have hpowers : (4877/50000 : ℝ)^5303 ≤ (145616191037523/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4877 : ℕ)^5303*25000000000000000000^1024 ≤ 145616191037523^1024*50000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4877 50000 145616191037523 25000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4877/50000 : ℝ)) (X := (145616191037523/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17391/100000 : ℝ) ^ (5303/1024 : ℝ) ≤ (11637520646788039/100000000000000000000 : ℝ) := by
    have hpowers : (17391/100000 : ℝ)^5303 ≤ (11637520646788039/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17391 : ℕ)^5303*100000000000000000000^1024 ≤ 11637520646788039^1024*100000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17391 100000 11637520646788039 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17391/100000 : ℝ)) (X := (11637520646788039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500145616191037523/12500000000000000000 : ℝ) ≤ (10000022494479173/10000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (12500145616191037523/12500000000000000000 : ℝ)^1024 ≤ (10000022494479173/10000000000000000 : ℝ)^5303 := by
      have hnat : (12500145616191037523 : ℕ)^1024*10000000000000000^5303 ≤ 10000022494479173^5303*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500145616191037523 12500000000000000000 10000022494479173 10000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000022494479173/10000000000000000 : ℝ)) (X := (12500145616191037523/12500000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012219985410938131/100000000000000000000 : ℝ) ≤ (5000117977071297/5000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (100012219985410938131/100000000000000000000 : ℝ)^1024 ≤ (5000117977071297/5000000000000000 : ℝ)^5303 := by
      have hnat : (100012219985410938131 : ℕ)^1024*5000000000000000^5303 ≤ 5000117977071297^5303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012219985410938131 100000000000000000000 5000117977071297 5000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000117977071297/5000000000000000 : ℝ)) (X := (100012219985410938131/100000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011637520646788039/50000000000000000000 : ℝ) ≤ (2000089882761203/2000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50011637520646788039/50000000000000000000 : ℝ)^1024 ≤ (2000089882761203/2000000000000000 : ℝ)^5303 := by
      have hnat : (50011637520646788039 : ℕ)^1024*2000000000000000^5303 ≤ 2000089882761203^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011637520646788039 50000000000000000000 2000089882761203 2000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000089882761203/2000000000000000 : ℝ)) (X := (50011637520646788039/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(145616191037523/25000000000000000000 : ℝ) ≤ ((76366007619223427333/76370000000000000000 : ℝ)+2*(213459663421/763700000000000 : ℝ)*(4877/50000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (76366007619223427333/76370000000000000000 : ℝ)+2*(213459663421/763700000000000 : ℝ)*(4877/50000 : ℝ)=(10000022494479173/10000000000000000 : ℝ) by norm_num, show 1+2*(145616191037523/25000000000000000000 : ℝ)=(12500145616191037523/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11637520646788039/100000000000000000000 : ℝ)+(145616191037523/25000000000000000000 : ℝ) ≤ ((76366007619223427333/76370000000000000000 : ℝ)+(213459663421/763700000000000 : ℝ)*((17391/100000 : ℝ)+(4877/50000 : ℝ)))^(5303/1024 : ℝ) := by
    rw [show (76366007619223427333/76370000000000000000 : ℝ)+(213459663421/763700000000000 : ℝ)*((17391/100000 : ℝ)+(4877/50000 : ℝ))=(5000117977071297/5000000000000000 : ℝ) by norm_num, show 1+(11637520646788039/100000000000000000000 : ℝ)+(145616191037523/25000000000000000000 : ℝ)=(100012219985410938131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11637520646788039/100000000000000000000 : ℝ) ≤ ((76366007619223427333/76370000000000000000 : ℝ)+2*(213459663421/763700000000000 : ℝ)*(17391/100000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (76366007619223427333/76370000000000000000 : ℝ)+2*(213459663421/763700000000000 : ℝ)*(17391/100000 : ℝ)=(2000089882761203/2000000000000000 : ℝ) by norm_num, show 1+2*(11637520646788039/100000000000000000000 : ℝ)=(50011637520646788039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (76366007619223427333/76370000000000000000 : ℝ)*(X 1 0+X 2 0)+(213459663421/763700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (4877/50000 : ℝ)) (hi := (17391/100000 : ℝ)) (c := (76366007619223427333/76370000000000000000 : ℝ)) (alpha := (213459663421/763700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (76366007619223427333/76370000000000000000 : ℝ)*(X 0 1+X 2 1)+(213459663421/763700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (4877/50000 : ℝ)) (hi := (17391/100000 : ℝ)) (c := (76366007619223427333/76370000000000000000 : ℝ)) (alpha := (213459663421/763700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (76366007619223427333/76370000000000000000 : ℝ)*(X 0 2+X 1 2)+(213459663421/763700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (4877/50000 : ℝ)) (hi := (17391/100000 : ℝ)) (c := (76366007619223427333/76370000000000000000 : ℝ)) (alpha := (213459663421/763700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-352084531/2500000000 : ℝ)*X 0 0+(218796053/400000000 : ℝ)*X 0 1+(5137995947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343323321/10000000000 : ℝ)*X 1 0+(-1580443703/10000000000 : ℝ)*X 1 1+(205519839/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33395773/62500000 : ℝ)*X 2 0+(1284498983/2500000000 : ℝ)*X 2 1+(-1580443281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2051666181/5000000000 : ℝ)*X 0 0+(909744453/2500000000 : ℝ)*X 0 1+(71928791/156250000 : ℝ)*X 0 2+(2051666181/5000000000 : ℝ)*X 1 0+(909744453/2500000000 : ℝ)*X 1 1+(71928791/156250000 : ℝ)*X 1 2+(2051666181/5000000000 : ℝ)*X 2 0+(909744453/2500000000 : ℝ)*X 2 1+(71928791/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-22007651/156250000 : ℝ)*X 0 0+(2570842551/5000000000 : ℝ)*X 0 1+(546615671/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627239179/5000000000 : ℝ)*X 1 0+(-1252282539/10000000000 : ℝ)*X 1 1+(1366539171/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627239157/5000000000 : ℝ)*X 2 0+(2733078349/5000000000 : ℝ)*X 2 1+(-62614129/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4103771887/10000000000 : ℝ)*X 0 0+(71761287/156250000 : ℝ)*X 0 1+(912464487/2500000000 : ℝ)*X 0 2+(4103771887/10000000000 : ℝ)*X 1 0+(71761287/156250000 : ℝ)*X 1 1+(912464487/2500000000 : ℝ)*X 1 2+(4103771887/10000000000 : ℝ)*X 2 0+(71761287/156250000 : ℝ)*X 2 1+(912464487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2829160497828978039729953109/272750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (489462189/50000000000000 : ℝ)*(base19) + (918203601/100000000000000 : ℝ)*(base23) + (28121823/20000000000000 : ℝ)*(lower2) + (39149009/50000000000000 : ℝ)*(upper3) + (37155049/20000000000000 : ℝ)*(upper5) + (1012444322112237/50000000000000 : ℝ)*(major0) + (1012444322112237/50000000000000 : ℝ)*(major1) + (1012444322112237/50000000000000 : ℝ)*(major2) + (301291446898707/10000000000000 : ℝ)*(sp0) + (3012925864839001/100000000000000 : ℝ)*(sp1) + (1506462962779889/50000000000000 : ℝ)*(sp2) + (1036847196203451/100000000000000 : ℝ)*(sp3) + (3093694077/25000000000000 : ℝ)*(sp4) + (725681161/25000000000000 : ℝ)*(sp7) + (207370019785619/20000000000000 : ℝ)*(f.failure) + (1506463421881689/50000000000000 : ℝ)*(f.sum) + (213869817449/170468750000000000000000000 : ℝ)*base66 + (1486673980567467703/545500000000000000000000000000000 : ℝ)*base67 + (2085305388179467703/545500000000000000000000000000000 : ℝ)*base69 + (1547729469498032297/545500000000000000000000000000000 : ℝ)*base72 + (4438861244267/5455000000000000000000000000 : ℝ)*base73 + (2050887814048032297/545500000000000000000000000000000 : ℝ)*base76 + (2141943011712532297/545500000000000000000000000000000 : ℝ)*base78 + (1327992517247532297/545500000000000000000000000000000 : ℝ)*base80 + (980925463117/1363750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16502937/2000000000000000000000 : ℝ)*base89 + (16502937/2000000000000000000000 : ℝ)*base91 + (16502937/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106018533310670956848627/7637000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235772731/12500000000000 : ℝ)*(base19) + (1003614669/50000000000000 : ℝ)*(base23) + (283365359/100000000000000 : ℝ)*(upper3) + (71549307/100000000000000 : ℝ)*(lower4) + (149710567/50000000000000 : ℝ)*(upper5) + (207126551739053/10000000000000 : ℝ)*(major0) + (207126551739053/10000000000000 : ℝ)*(major1) + (207126551739053/10000000000000 : ℝ)*(major2) + (17180207629/100000000000000 : ℝ)*(sp1) + (17812163957/100000000000000 : ℝ)*(sp2) + (308193306079531/10000000000000 : ℝ)*(sp4) + (1540956997202917/50000000000000 : ℝ)*(sp5) + (616382648280403/20000000000000 : ℝ)*(sp6) + (1060597511244991/100000000000000 : ℝ)*(sp7) + (1060597511244991/100000000000000 : ℝ)*(f.failure) + (308193306079531/10000000000000 : ℝ)*(f.sum) + (5051243595123/7637000000000000000000000000 : ℝ)*base66 + (7047724091935435649/763700000000000000000000000000000 : ℝ)*base67 + (453901117226564351/763700000000000000000000000000000 : ℝ)*base70 + (864127100967564351/763700000000000000000000000000000 : ℝ)*base72 + (26035746859551/7637000000000000000000000000 : ℝ)*base73 + (3433062460021264351/763700000000000000000000000000000 : ℝ)*base76 + (1599379709833135649/763700000000000000000000000000000 : ℝ)*base77 + (6522682041931635649/763700000000000000000000000000000 : ℝ)*base79 + (28141137830461/7637000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (85495907/10000000000000000000000 : ℝ)*base90 + (85495907/10000000000000000000000 : ℝ)*base92 + (85495907/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1711_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17391/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4877/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1711_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1711_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1711_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1711_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1711_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1711_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

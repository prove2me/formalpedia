-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:40.764046+00:00
-- url     : https://prove2.me/submissions/02d5cefc-bf2c-40c9-bc4a-307a050b66a4

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
theorem support_rectangle_w1141_s0_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-946063557/5000000000 : ℝ)*x 0 + (94602523/156250000 : ℝ)*x 1 + (4780345789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946063557/5000000000 : ℝ)^4167 ≤ (2749908794967/25000000000000 : ℝ)^3143 := by
    have hnat : (946063557 : ℕ)^4167*25000000000000^3143 ≤ 2749908794967^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946063557 5000000000 2749908794967 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94602523/156250000 : ℝ)^4167 ≤ (411314941789/800000000000 : ℝ)^3143 := by
    have hnat : (94602523 : ℕ)^4167*800000000000^3143 ≤ 411314941789^3143*156250000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94602523 156250000 411314941789 800000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4780345789/10000000000 : ℝ)^4167 ≤ (3758599708221/10000000000000 : ℝ)^3143 := by
    have hnat : (4780345789 : ℕ)^4167*10000000000000^3143 ≤ 3758599708221^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780345789 10000000000 3758599708221 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946063557/5000000000 : ℝ), (94602523/156250000 : ℝ), (4780345789/10000000000 : ℝ)] ![(2749908794967/25000000000000 : ℝ), (411314941789/800000000000 : ℝ), (3758599708221/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946063557/5000000000 : ℝ)|^4167 ≤ (2749908794967/25000000000000 : ℝ)^3143
        have hw : |(-946063557/5000000000 : ℝ)|=(946063557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(94602523/156250000 : ℝ)|^4167 ≤ (411314941789/800000000000 : ℝ)^3143
        have hw : |(94602523/156250000 : ℝ)|=(94602523/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4780345789/10000000000 : ℝ)|^4167 ≤ (3758599708221/10000000000000 : ℝ)^3143
        have hw : |(4780345789/10000000000 : ℝ)|=(4780345789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5516850349/10000000000 : ℝ)*x 0 + (-524681161/2000000000 : ℝ)*x 1 + (239017281/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516850349/10000000000 : ℝ)^4167 ≤ (90899882519/200000000000 : ℝ)^3143 := by
    have hnat : (5516850349 : ℕ)^4167*200000000000^3143 ≤ 90899882519^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516850349 10000000000 90899882519 200000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524681161/2000000000 : ℝ)^4167 ≤ (4241015852159/25000000000000 : ℝ)^3143 := by
    have hnat : (524681161 : ℕ)^4167*25000000000000^3143 ≤ 4241015852159^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524681161 2000000000 4241015852159 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239017281/500000000 : ℝ)^4167 ≤ (9396498830127/25000000000000 : ℝ)^3143 := by
    have hnat : (239017281 : ℕ)^4167*25000000000000^3143 ≤ 9396498830127^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239017281 500000000 9396498830127 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516850349/10000000000 : ℝ), (-524681161/2000000000 : ℝ), (239017281/500000000 : ℝ)] ![(90899882519/200000000000 : ℝ), (4241015852159/25000000000000 : ℝ), (9396498830127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516850349/10000000000 : ℝ)|^4167 ≤ (90899882519/200000000000 : ℝ)^3143
        have hw : |(5516850349/10000000000 : ℝ)|=(5516850349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524681161/2000000000 : ℝ)|^4167 ≤ (4241015852159/25000000000000 : ℝ)^3143
        have hw : |(-524681161/2000000000 : ℝ)|=(524681161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239017281/500000000 : ℝ)|^4167 ≤ (9396498830127/25000000000000 : ℝ)^3143
        have hw : |(239017281/500000000 : ℝ)|=(239017281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2758424777/5000000000 : ℝ)*x 0 + (2390172987/5000000000 : ℝ)*x 1 + (-1311703193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758424777/5000000000 : ℝ)^4167 ≤ (45449932576129/100000000000000 : ℝ)^3143 := by
    have hnat : (2758424777 : ℕ)^4167*100000000000000^3143 ≤ 45449932576129^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758424777 5000000000 45449932576129 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2390172987/5000000000 : ℝ)^4167 ≤ (37585999010701/100000000000000 : ℝ)^3143 := by
    have hnat : (2390172987 : ℕ)^4167*100000000000000^3143 ≤ 37585999010701^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390172987 5000000000 37585999010701 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311703193/5000000000 : ℝ)^4167 ≤ (2120508548709/12500000000000 : ℝ)^3143 := by
    have hnat : (1311703193 : ℕ)^4167*12500000000000^3143 ≤ 2120508548709^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311703193 5000000000 2120508548709 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758424777/5000000000 : ℝ), (2390172987/5000000000 : ℝ), (-1311703193/5000000000 : ℝ)] ![(45449932576129/100000000000000 : ℝ), (37585999010701/100000000000000 : ℝ), (2120508548709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758424777/5000000000 : ℝ)|^4167 ≤ (45449932576129/100000000000000 : ℝ)^3143
        have hw : |(2758424777/5000000000 : ℝ)|=(2758424777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2390172987/5000000000 : ℝ)|^4167 ≤ (37585999010701/100000000000000 : ℝ)^3143
        have hw : |(2390172987/5000000000 : ℝ)|=(2390172987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1311703193/5000000000 : ℝ)|^4167 ≤ (2120508548709/12500000000000 : ℝ)^3143
        have hw : |(-1311703193/5000000000 : ℝ)|=(1311703193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201071517/10000000000 : ℝ)*x 0 + (3121124857/10000000000 : ℝ)*x 1 + (5655646611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201071517/10000000000 : ℝ)^4167 ≤ (15835052999603/50000000000000 : ℝ)^3143 := by
    have hnat : (4201071517 : ℕ)^4167*50000000000000^3143 ≤ 15835052999603^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201071517 10000000000 15835052999603 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121124857/10000000000 : ℝ)^4167 ≤ (10678887505221/50000000000000 : ℝ)^3143 := by
    have hnat : (3121124857 : ℕ)^4167*50000000000000^3143 ≤ 10678887505221^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121124857 10000000000 10678887505221 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5655646611/10000000000 : ℝ)^4167 ≤ (23486059488279/50000000000000 : ℝ)^3143 := by
    have hnat : (5655646611 : ℕ)^4167*50000000000000^3143 ≤ 23486059488279^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655646611 10000000000 23486059488279 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201071517/10000000000 : ℝ), (3121124857/10000000000 : ℝ), (5655646611/10000000000 : ℝ)] ![(15835052999603/50000000000000 : ℝ), (10678887505221/50000000000000 : ℝ), (23486059488279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201071517/10000000000 : ℝ)|^4167 ≤ (15835052999603/50000000000000 : ℝ)^3143
        have hw : |(4201071517/10000000000 : ℝ)|=(4201071517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121124857/10000000000 : ℝ)|^4167 ≤ (10678887505221/50000000000000 : ℝ)^3143
        have hw : |(3121124857/10000000000 : ℝ)|=(3121124857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5655646611/10000000000 : ℝ)|^4167 ≤ (23486059488279/50000000000000 : ℝ)^3143
        have hw : |(5655646611/10000000000 : ℝ)|=(5655646611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-948637893/5000000000 : ℝ)*x 0 + (2406608723/5000000000 : ℝ)*x 1 + (3010267027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948637893/5000000000 : ℝ)^4167 ≤ (11039335560237/100000000000000 : ℝ)^3143 := by
    have hnat : (948637893 : ℕ)^4167*100000000000000^3143 ≤ 11039335560237^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948637893 5000000000 11039335560237 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406608723/5000000000 : ℝ)^4167 ≤ (18964521772681/50000000000000 : ℝ)^3143 := by
    have hnat : (2406608723 : ℕ)^4167*50000000000000^3143 ≤ 18964521772681^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406608723 5000000000 18964521772681 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010267027/5000000000 : ℝ)^4167 ≤ (10206324174399/20000000000000 : ℝ)^3143 := by
    have hnat : (3010267027 : ℕ)^4167*20000000000000^3143 ≤ 10206324174399^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010267027 5000000000 10206324174399 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948637893/5000000000 : ℝ), (2406608723/5000000000 : ℝ), (3010267027/5000000000 : ℝ)] ![(11039335560237/100000000000000 : ℝ), (18964521772681/50000000000000 : ℝ), (10206324174399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948637893/5000000000 : ℝ)|^4167 ≤ (11039335560237/100000000000000 : ℝ)^3143
        have hw : |(-948637893/5000000000 : ℝ)|=(948637893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406608723/5000000000 : ℝ)|^4167 ≤ (18964521772681/50000000000000 : ℝ)^3143
        have hw : |(2406608723/5000000000 : ℝ)|=(2406608723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010267027/5000000000 : ℝ)|^4167 ≤ (10206324174399/20000000000000 : ℝ)^3143
        have hw : |(3010267027/5000000000 : ℝ)|=(3010267027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034124393/2000000000 : ℝ)*x 0 + (-345804471/2500000000 : ℝ)*x 1 + (3010266963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034124393/2000000000 : ℝ)^4167 ≤ (20853745299627/50000000000000 : ℝ)^3143 := by
    have hnat : (1034124393 : ℕ)^4167*50000000000000^3143 ≤ 20853745299627^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034124393 2000000000 20853745299627 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345804471/2500000000 : ℝ)^4167 ≤ (290435597723/4000000000000 : ℝ)^3143 := by
    have hnat : (345804471 : ℕ)^4167*4000000000000^3143 ≤ 290435597723^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345804471 2500000000 290435597723 4000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010266963/5000000000 : ℝ)^4167 ≤ (51031619433549/100000000000000 : ℝ)^3143 := by
    have hnat : (3010266963 : ℕ)^4167*100000000000000^3143 ≤ 51031619433549^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010266963 5000000000 51031619433549 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034124393/2000000000 : ℝ), (-345804471/2500000000 : ℝ), (3010266963/5000000000 : ℝ)] ![(20853745299627/50000000000000 : ℝ), (290435597723/4000000000000 : ℝ), (51031619433549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034124393/2000000000 : ℝ)|^4167 ≤ (20853745299627/50000000000000 : ℝ)^3143
        have hw : |(1034124393/2000000000 : ℝ)|=(1034124393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345804471/2500000000 : ℝ)|^4167 ≤ (290435597723/4000000000000 : ℝ)^3143
        have hw : |(-345804471/2500000000 : ℝ)|=(345804471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010266963/5000000000 : ℝ)|^4167 ≤ (51031619433549/100000000000000 : ℝ)^3143
        have hw : |(3010266963/5000000000 : ℝ)|=(3010266963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5170621971/10000000000 : ℝ)*x 0 + (6020533947/10000000000 : ℝ)*x 1 + (-691608921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170621971/10000000000 : ℝ)^4167 ≤ (41707490663419/100000000000000 : ℝ)^3143 := by
    have hnat : (5170621971 : ℕ)^4167*100000000000000^3143 ≤ 41707490663419^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170621971 10000000000 41707490663419 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6020533947/10000000000 : ℝ)^4167 ≤ (6378952458693/12500000000000 : ℝ)^3143 := by
    have hnat : (6020533947 : ℕ)^4167*12500000000000^3143 ≤ 6378952458693^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020533947 10000000000 6378952458693 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691608921/5000000000 : ℝ)^4167 ≤ (907611206347/12500000000000 : ℝ)^3143 := by
    have hnat : (691608921 : ℕ)^4167*12500000000000^3143 ≤ 907611206347^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691608921 5000000000 907611206347 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170621971/10000000000 : ℝ), (6020533947/10000000000 : ℝ), (-691608921/5000000000 : ℝ)] ![(41707490663419/100000000000000 : ℝ), (6378952458693/12500000000000 : ℝ), (907611206347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170621971/10000000000 : ℝ)|^4167 ≤ (41707490663419/100000000000000 : ℝ)^3143
        have hw : |(5170621971/10000000000 : ℝ)|=(5170621971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6020533947/10000000000 : ℝ)|^4167 ≤ (6378952458693/12500000000000 : ℝ)^3143
        have hw : |(6020533947/10000000000 : ℝ)|=(6020533947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-691608921/5000000000 : ℝ)|^4167 ≤ (907611206347/12500000000000 : ℝ)^3143
        have hw : |(-691608921/5000000000 : ℝ)|=(691608921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s0_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211312703/10000000000 : ℝ)*x 0 + (1397565463/2500000000 : ℝ)*x 1 + (3188808151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211312703/10000000000 : ℝ)^4167 ≤ (992890747597/3125000000000 : ℝ)^3143 := by
    have hnat : (4211312703 : ℕ)^4167*3125000000000^3143 ≤ 992890747597^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211312703 10000000000 992890747597 3125000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397565463/2500000000 : ℝ)^4167 ≤ (289084436693/625000000000 : ℝ)^3143 := by
    have hnat : (1397565463 : ℕ)^4167*625000000000^3143 ≤ 289084436693^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397565463 2500000000 289084436693 625000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188808151/10000000000 : ℝ)^4167 ≤ (10986993098091/50000000000000 : ℝ)^3143 := by
    have hnat : (3188808151 : ℕ)^4167*50000000000000^3143 ≤ 10986993098091^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188808151 10000000000 10986993098091 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211312703/10000000000 : ℝ), (1397565463/2500000000 : ℝ), (3188808151/10000000000 : ℝ)] ![(992890747597/3125000000000 : ℝ), (289084436693/625000000000 : ℝ), (10986993098091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211312703/10000000000 : ℝ)|^4167 ≤ (992890747597/3125000000000 : ℝ)^3143
        have hw : |(4211312703/10000000000 : ℝ)|=(4211312703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1397565463/2500000000 : ℝ)|^4167 ≤ (289084436693/625000000000 : ℝ)^3143
        have hw : |(1397565463/2500000000 : ℝ)|=(1397565463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188808151/10000000000 : ℝ)|^4167 ≤ (10986993098091/50000000000000 : ℝ)^3143
        have hw : |(3188808151/10000000000 : ℝ)|=(3188808151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27819/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8333/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8333 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8333*1^2048 ≤ 0^2048*1^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8333/2048 : ℝ) ≤ (300436532835097581/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8333 ≤ (300436532835097581/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8333*12500000000000000000^2048 ≤ 300436532835097581^2048*5^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 300436532835097581 12500000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (300436532835097581/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8333 := by
      have hnat : (1 : ℕ)^2048*1^8333 ≤ 1^8333*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12800436532835097581/12500000000000000000 : ℝ) ≤ (10058542579371007/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (12800436532835097581/12500000000000000000 : ℝ)^2048 ≤ (10058542579371007/10000000000000000 : ℝ)^8333 := by
      have hnat : (12800436532835097581 : ℕ)^2048*10000000000000000^8333 ≤ 10058542579371007^8333*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12800436532835097581 12500000000000000000 10058542579371007 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058542579371007/10000000000000000 : ℝ)) (X := (12800436532835097581/12500000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6550436532835097581/6250000000000000000 : ℝ) ≤ (5058542579371007/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (6550436532835097581/6250000000000000000 : ℝ)^2048 ≤ (5058542579371007/5000000000000000 : ℝ)^8333 := by
      have hnat : (6550436532835097581 : ℕ)^2048*5000000000000000^8333 ≤ 5058542579371007^8333*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6550436532835097581 6250000000000000000 5058542579371007 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058542579371007/5000000000000000 : ℝ)) (X := (6550436532835097581/6250000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58542579371007/4000000000000000 : ℝ)*(0 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58542579371007/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(300436532835097581/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58542579371007/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (1 : ℝ)+(58542579371007/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058542579371007/10000000000000000 : ℝ) by norm_num, show 1+(300436532835097581/12500000000000000000 : ℝ)+(0 : ℝ)=(12800436532835097581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(300436532835097581/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58542579371007/4000000000000000 : ℝ)*(2/5 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58542579371007/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058542579371007/5000000000000000 : ℝ) by norm_num, show 1+2*(300436532835097581/12500000000000000000 : ℝ)=(6550436532835097581/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58542579371007/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58542579371007/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58542579371007/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58542579371007/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58542579371007/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58542579371007/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-946063557/5000000000 : ℝ)*X 0 0+(94602523/156250000 : ℝ)*X 0 1+(4780345789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516850349/10000000000 : ℝ)*X 1 0+(-524681161/2000000000 : ℝ)*X 1 1+(239017281/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2758424777/5000000000 : ℝ)*X 2 0+(2390172987/5000000000 : ℝ)*X 2 1+(-1311703193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4201071517/10000000000 : ℝ)*X 0 0+(3121124857/10000000000 : ℝ)*X 0 1+(5655646611/10000000000 : ℝ)*X 0 2+(4201071517/10000000000 : ℝ)*X 1 0+(3121124857/10000000000 : ℝ)*X 1 1+(5655646611/10000000000 : ℝ)*X 1 2+(4201071517/10000000000 : ℝ)*X 2 0+(3121124857/10000000000 : ℝ)*X 2 1+(5655646611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-948637893/5000000000 : ℝ)*X 0 0+(2406608723/5000000000 : ℝ)*X 0 1+(3010267027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034124393/2000000000 : ℝ)*X 1 0+(-345804471/2500000000 : ℝ)*X 1 1+(3010266963/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170621971/10000000000 : ℝ)*X 2 0+(6020533947/10000000000 : ℝ)*X 2 1+(-691608921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211312703/10000000000 : ℝ)*X 0 0+(1397565463/2500000000 : ℝ)*X 0 1+(3188808151/10000000000 : ℝ)*X 0 2+(4211312703/10000000000 : ℝ)*X 1 0+(1397565463/2500000000 : ℝ)*X 1 1+(3188808151/10000000000 : ℝ)*X 1 2+(4211312703/10000000000 : ℝ)*X 2 0+(1397565463/2500000000 : ℝ)*X 2 1+(3188808151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (446989088274081681/62500000000000000000000 : ℝ) := by norm_num
    linear_combination (8566593/10000000000000 : ℝ)*(base1) + (172765909/10000000000000 : ℝ)*(base19) + (1555160341/100000000000000 : ℝ)*(base23) + (29702659/50000000000000 : ℝ)*(base24) + (37554259/10000000000000 : ℝ)*(upper3) + (589681471740847/100000000000000 : ℝ)*(major0) + (589681471740847/100000000000000 : ℝ)*(major1) + (589681471740847/100000000000000 : ℝ)*(major2) + (784802335529181/100000000000000 : ℝ)*(sp0) + (784804328249237/100000000000000 : ℝ)*(sp1) + (196201110335667/25000000000000 : ℝ)*(sp2) + (394553605208587/100000000000000 : ℝ)*(sp3) + (152241803/4000000000000 : ℝ)*(sp4) + (2958304661/100000000000000 : ℝ)*(sp7) + (394556649179177/100000000000000 : ℝ)*(f.failure) + (392403027954163/50000000000000 : ℝ)*(f.sum) + (397700946177071/200000000000000000000000000000 : ℝ)*base66 + (835077724222929/400000000000000000000000000000 : ℝ)*base67 + (3265133238622929/400000000000000000000000000000 : ℝ)*base69 + (914667019422929/400000000000000000000000000000 : ℝ)*base71 + (184193119777071/200000000000000000000000000000 : ℝ)*base74 + (1448802393777071/400000000000000000000000000000 : ℝ)*base76 + (451147524177071/400000000000000000000000000000 : ℝ)*base78 + (490467424222929/400000000000000000000000000000 : ℝ)*base79 + (1655358045422929/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (92344131/10000000000000000000000 : ℝ)*base90 + (92344131/10000000000000000000000 : ℝ)*base92 + (92344131/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (291827949117429464549841/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14782079/20000000000000 : ℝ)*(base1) + (35964111/2500000000000 : ℝ)*(base19) + (17984933/1250000000000 : ℝ)*(base23) + (155863013/100000000000000 : ℝ)*(upper3) + (169275423/100000000000000 : ℝ)*(upper5) + (622348915941579/100000000000000 : ℝ)*(major0) + (622348915941579/100000000000000 : ℝ)*(major1) + (622348915941579/100000000000000 : ℝ)*(major2) + (58299017/2000000000000 : ℝ)*(sp1) + (363005199/12500000000000 : ℝ)*(sp2) + (828283232134261/100000000000000 : ℝ)*(sp4) + (33131152188343/4000000000000 : ℝ)*(sp5) + (414139407693817/50000000000000 : ℝ)*(sp6) + (16656576207877/4000000000000 : ℝ)*(sp7) + (416414479107321/100000000000000 : ℝ)*(f.failure) + (165656631644773/20000000000000 : ℝ)*(f.sum) + (257702152600053/200000000000000000000000000000 : ℝ)*base65 + (1558359976000053/400000000000000000000000000000 : ℝ)*base67 + (191945070800053/400000000000000000000000000000 : ℝ)*base69 + (719044941599947/400000000000000000000000000000 : ℝ)*base72 + (1082775868400053/200000000000000000000000000000 : ℝ)*base73 + (1314837728400053/400000000000000000000000000000 : ℝ)*base75 + (318731035600053/400000000000000000000000000000 : ℝ)*base77 + (940537863999947/400000000000000000000000000000 : ℝ)*base80 + (1243696311400053/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (36876237/10000000000000000000000 : ℝ)*base89 + (36876237/10000000000000000000000 : ℝ)*base91 + (36876237/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1141_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27819/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_s1_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048431767/5000000000 : ℝ)*x 0 + (1140356069/2000000000 : ℝ)*x 1 + (200082177/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048431767/5000000000 : ℝ)^4167 ≤ (3151196229147/25000000000000 : ℝ)^3143 := by
    have hnat : (1048431767 : ℕ)^4167*25000000000000^3143 ≤ 3151196229147^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048431767 5000000000 3151196229147 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140356069/2000000000 : ℝ)^4167 ≤ (23740391645983/50000000000000 : ℝ)^3143 := by
    have hnat : (1140356069 : ℕ)^4167*50000000000000^3143 ≤ 23740391645983^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140356069 2000000000 23740391645983 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200082177/400000000 : ℝ)^4167 ≤ (7982886355203/20000000000000 : ℝ)^3143 := by
    have hnat : (200082177 : ℕ)^4167*20000000000000^3143 ≤ 7982886355203^3143*400000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200082177 400000000 7982886355203 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048431767/5000000000 : ℝ), (1140356069/2000000000 : ℝ), (200082177/400000000 : ℝ)] ![(3151196229147/25000000000000 : ℝ), (23740391645983/50000000000000 : ℝ), (7982886355203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048431767/5000000000 : ℝ)|^4167 ≤ (3151196229147/25000000000000 : ℝ)^3143
        have hw : |(-1048431767/5000000000 : ℝ)|=(1048431767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140356069/2000000000 : ℝ)|^4167 ≤ (23740391645983/50000000000000 : ℝ)^3143
        have hw : |(1140356069/2000000000 : ℝ)|=(1140356069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200082177/400000000 : ℝ)|^4167 ≤ (7982886355203/20000000000000 : ℝ)^3143
        have hw : |(200082177/400000000 : ℝ)|=(200082177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5419178099/10000000000 : ℝ)*x 0 + (-2474493753/10000000000 : ℝ)*x 1 + (4001643/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419178099/10000000000 : ℝ)^4167 ≤ (22193103612777/50000000000000 : ℝ)^3143 := by
    have hnat : (5419178099 : ℕ)^4167*50000000000000^3143 ≤ 22193103612777^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419178099 10000000000 22193103612777 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2474493753/10000000000 : ℝ)^4167 ≤ (15699368117951/100000000000000 : ℝ)^3143 := by
    have hnat : (2474493753 : ℕ)^4167*100000000000000^3143 ≤ 15699368117951^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2474493753 10000000000 15699368117951 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4001643/8000000 : ℝ)^4167 ≤ (19957212317463/50000000000000 : ℝ)^3143 := by
    have hnat : (4001643 : ℕ)^4167*50000000000000^3143 ≤ 19957212317463^3143*8000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001643 8000000 19957212317463 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419178099/10000000000 : ℝ), (-2474493753/10000000000 : ℝ), (4001643/8000000 : ℝ)] ![(22193103612777/50000000000000 : ℝ), (15699368117951/100000000000000 : ℝ), (19957212317463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419178099/10000000000 : ℝ)|^4167 ≤ (22193103612777/50000000000000 : ℝ)^3143
        have hw : |(5419178099/10000000000 : ℝ)|=(5419178099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2474493753/10000000000 : ℝ)|^4167 ≤ (15699368117951/100000000000000 : ℝ)^3143
        have hw : |(-2474493753/10000000000 : ℝ)|=(2474493753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4001643/8000000 : ℝ)|^4167 ≤ (19957212317463/50000000000000 : ℝ)^3143
        have hw : |(4001643/8000000 : ℝ)|=(4001643/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5419180021/10000000000 : ℝ)*x 0 + (125051301/250000000 : ℝ)*x 1 + (-1237246711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419180021/10000000000 : ℝ)^4167 ≤ (2219311404837/5000000000000 : ℝ)^3143 := by
    have hnat : (5419180021 : ℕ)^4167*5000000000000^3143 ≤ 2219311404837^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419180021 10000000000 2219311404837 5000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125051301/250000000 : ℝ)^4167 ≤ (3991440654417/10000000000000 : ℝ)^3143 := by
    have hnat : (125051301 : ℕ)^4167*10000000000000^3143 ≤ 3991440654417^3143*250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125051301 250000000 3991440654417 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237246711/5000000000 : ℝ)^4167 ≤ (3139873066747/20000000000000 : ℝ)^3143 := by
    have hnat : (1237246711 : ℕ)^4167*20000000000000^3143 ≤ 3139873066747^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237246711 5000000000 3139873066747 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419180021/10000000000 : ℝ), (125051301/250000000 : ℝ), (-1237246711/5000000000 : ℝ)] ![(2219311404837/5000000000000 : ℝ), (3991440654417/10000000000000 : ℝ), (3139873066747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419180021/10000000000 : ℝ)|^4167 ≤ (2219311404837/5000000000000 : ℝ)^3143
        have hw : |(5419180021/10000000000 : ℝ)|=(5419180021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125051301/250000000 : ℝ)|^4167 ≤ (3991440654417/10000000000000 : ℝ)^3143
        have hw : |(125051301/250000000 : ℝ)|=(125051301/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1237246711/5000000000 : ℝ)|^4167 ≤ (3139873066747/20000000000000 : ℝ)^3143
        have hw : |(-1237246711/5000000000 : ℝ)|=(1237246711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079380503/2500000000 : ℝ)*x 0 + (183842087/500000000 : ℝ)*x 1 + (39598849/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079380503/2500000000 : ℝ)^4167 ≤ (32839213710239/100000000000000 : ℝ)^3143 := by
    have hnat : (1079380503 : ℕ)^4167*100000000000000^3143 ≤ 32839213710239^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079380503 2500000000 32839213710239 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183842087/500000000 : ℝ)^4167 ≤ (13270131014167/50000000000000 : ℝ)^3143 := by
    have hnat : (183842087 : ℕ)^4167*50000000000000^3143 ≤ 13270131014167^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183842087 500000000 13270131014167 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39598849/78125000 : ℝ)^4167 ≤ (634695691367/1562500000000 : ℝ)^3143 := by
    have hnat : (39598849 : ℕ)^4167*1562500000000^3143 ≤ 634695691367^3143*78125000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39598849 78125000 634695691367 1562500000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079380503/2500000000 : ℝ), (183842087/500000000 : ℝ), (39598849/78125000 : ℝ)] ![(32839213710239/100000000000000 : ℝ), (13270131014167/50000000000000 : ℝ), (634695691367/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079380503/2500000000 : ℝ)|^4167 ≤ (32839213710239/100000000000000 : ℝ)^3143
        have hw : |(1079380503/2500000000 : ℝ)|=(1079380503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183842087/500000000 : ℝ)|^4167 ≤ (13270131014167/50000000000000 : ℝ)^3143
        have hw : |(183842087/500000000 : ℝ)|=(183842087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39598849/78125000 : ℝ)|^4167 ≤ (634695691367/1562500000000 : ℝ)^3143
        have hw : |(39598849/78125000 : ℝ)|=(39598849/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32776117/156250000 : ℝ)*x 0 + (5011612091/10000000000 : ℝ)*x 1 + (5692032973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32776117/156250000 : ℝ)^4167 ≤ (6305612253789/50000000000000 : ℝ)^3143 := by
    have hnat : (32776117 : ℕ)^4167*50000000000000^3143 ≤ 6305612253789^3143*156250000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32776117 156250000 6305612253789 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011612091/10000000000 : ℝ)^4167 ≤ (40015577518929/100000000000000 : ℝ)^3143 := by
    have hnat : (5011612091 : ℕ)^4167*100000000000000^3143 ≤ 40015577518929^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011612091 10000000000 40015577518929 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5692032973/10000000000 : ℝ)^4167 ≤ (47373197964883/100000000000000 : ℝ)^3143 := by
    have hnat : (5692032973 : ℕ)^4167*100000000000000^3143 ≤ 47373197964883^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5692032973 10000000000 47373197964883 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32776117/156250000 : ℝ), (5011612091/10000000000 : ℝ), (5692032973/10000000000 : ℝ)] ![(6305612253789/50000000000000 : ℝ), (40015577518929/100000000000000 : ℝ), (47373197964883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32776117/156250000 : ℝ)|^4167 ≤ (6305612253789/50000000000000 : ℝ)^3143
        have hw : |(-32776117/156250000 : ℝ)|=(32776117/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011612091/10000000000 : ℝ)|^4167 ≤ (40015577518929/100000000000000 : ℝ)^3143
        have hw : |(5011612091/10000000000 : ℝ)|=(5011612091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5692032973/10000000000 : ℝ)|^4167 ≤ (47373197964883/100000000000000 : ℝ)^3143
        have hw : |(5692032973/10000000000 : ℝ)|=(5692032973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (327486881/625000000 : ℝ)*x 0 + (-1784514279/10000000000 : ℝ)*x 1 + (8893801/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327486881/625000000 : ℝ)^4167 ≤ (21224399547763/50000000000000 : ℝ)^3143 := by
    have hnat : (327486881 : ℕ)^4167*50000000000000^3143 ≤ 21224399547763^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327486881 625000000 21224399547763 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784514279/10000000000 : ℝ)^4167 ≤ (10178006595691/100000000000000 : ℝ)^3143 := by
    have hnat : (1784514279 : ℕ)^4167*100000000000000^3143 ≤ 10178006595691^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784514279 10000000000 10178006595691 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8893801/15625000 : ℝ)^4167 ≤ (1480412321577/3125000000000 : ℝ)^3143 := by
    have hnat : (8893801 : ℕ)^4167*3125000000000^3143 ≤ 1480412321577^3143*15625000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8893801 15625000 1480412321577 3125000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327486881/625000000 : ℝ), (-1784514279/10000000000 : ℝ), (8893801/15625000 : ℝ)] ![(21224399547763/50000000000000 : ℝ), (10178006595691/100000000000000 : ℝ), (1480412321577/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327486881/625000000 : ℝ)|^4167 ≤ (21224399547763/50000000000000 : ℝ)^3143
        have hw : |(327486881/625000000 : ℝ)|=(327486881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784514279/10000000000 : ℝ)|^4167 ≤ (10178006595691/100000000000000 : ℝ)^3143
        have hw : |(-1784514279/10000000000 : ℝ)|=(1784514279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8893801/15625000 : ℝ)|^4167 ≤ (1480412321577/3125000000000 : ℝ)^3143
        have hw : |(8893801/15625000 : ℝ)|=(8893801/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5239790159/10000000000 : ℝ)*x 0 + (1423008209/2500000000 : ℝ)*x 1 + (-111532119/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239790159/10000000000 : ℝ)^4167 ≤ (42448799772187/100000000000000 : ℝ)^3143 := by
    have hnat : (5239790159 : ℕ)^4167*100000000000000^3143 ≤ 42448799772187^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239790159 10000000000 42448799772187 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423008209/2500000000 : ℝ)^4167 ≤ (9474639290637/20000000000000 : ℝ)^3143 := by
    have hnat : (1423008209 : ℕ)^4167*20000000000000^3143 ≤ 9474639290637^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423008209 2500000000 9474639290637 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111532119/625000000 : ℝ)^4167 ≤ (5089001880019/50000000000000 : ℝ)^3143 := by
    have hnat : (111532119 : ℕ)^4167*50000000000000^3143 ≤ 5089001880019^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111532119 625000000 5089001880019 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239790159/10000000000 : ℝ), (1423008209/2500000000 : ℝ), (-111532119/625000000 : ℝ)] ![(42448799772187/100000000000000 : ℝ), (9474639290637/20000000000000 : ℝ), (5089001880019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239790159/10000000000 : ℝ)|^4167 ≤ (42448799772187/100000000000000 : ℝ)^3143
        have hw : |(5239790159/10000000000 : ℝ)|=(5239790159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423008209/2500000000 : ℝ)|^4167 ≤ (9474639290637/20000000000000 : ℝ)^3143
        have hw : |(1423008209/2500000000 : ℝ)|=(1423008209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111532119/625000000 : ℝ)|^4167 ≤ (5089001880019/50000000000000 : ℝ)^3143
        have hw : |(-111532119/625000000 : ℝ)|=(111532119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s1_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863825009/2000000000 : ℝ)*x 0 + (5049642801/10000000000 : ℝ)*x 1 + (739245749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863825009/2000000000 : ℝ)^4167 ≤ (32855379839101/100000000000000 : ℝ)^3143 := by
    have hnat : (863825009 : ℕ)^4167*100000000000000^3143 ≤ 32855379839101^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863825009 2000000000 32855379839101 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5049642801/10000000000 : ℝ)^4167 ≤ (20209333199603/50000000000000 : ℝ)^3143 := by
    have hnat : (5049642801 : ℕ)^4167*50000000000000^3143 ≤ 20209333199603^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049642801 10000000000 20209333199603 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739245749/2000000000 : ℝ)^4167 ≤ (5345190749899/20000000000000 : ℝ)^3143 := by
    have hnat : (739245749 : ℕ)^4167*20000000000000^3143 ≤ 5345190749899^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739245749 2000000000 5345190749899 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863825009/2000000000 : ℝ), (5049642801/10000000000 : ℝ), (739245749/2000000000 : ℝ)] ![(32855379839101/100000000000000 : ℝ), (20209333199603/50000000000000 : ℝ), (5345190749899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863825009/2000000000 : ℝ)|^4167 ≤ (32855379839101/100000000000000 : ℝ)^3143
        have hw : |(863825009/2000000000 : ℝ)|=(863825009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5049642801/10000000000 : ℝ)|^4167 ≤ (20209333199603/50000000000000 : ℝ)^3143
        have hw : |(5049642801/10000000000 : ℝ)|=(5049642801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(739245749/2000000000 : ℝ)|^4167 ≤ (5345190749899/20000000000000 : ℝ)^3143
        have hw : |(739245749/2000000000 : ℝ)|=(739245749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27819/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10221/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27819/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27819/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27819/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27819/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27819/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27819/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (409/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (19163109417/100000000000000000000 : ℝ) := by
    have hpowers : (409/100000 : ℝ)^8333 ≤ (19163109417/100000000000000000000 : ℝ)^2048 := by
      have hnat : (409 : ℕ)^8333*100000000000000000000^2048 ≤ 19163109417^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        409 100000 19163109417 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (409/100000 : ℝ)) (X := (19163109417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27819/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (68552024749425717/12500000000000000000 : ℝ) := by
    have hpowers : (27819/100000 : ℝ)^8333 ≤ (68552024749425717/12500000000000000000 : ℝ)^2048 := by
      have hnat : (27819 : ℕ)^8333*12500000000000000000^2048 ≤ 68552024749425717^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27819 100000 68552024749425717 12500000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27819/100000 : ℝ)) (X := (68552024749425717/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000019163109417/50000000000000000000 : ℝ) ≤ (10000000000941943/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50000000019163109417/50000000000000000000 : ℝ)^2048 ≤ (10000000000941943/10000000000000000 : ℝ)^8333 := by
      have hnat : (50000000019163109417 : ℕ)^2048*10000000000000000^8333 ≤ 10000000000941943^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000019163109417 50000000000000000000 10000000000941943 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000941943/10000000000000000 : ℝ)) (X := (50000000019163109417/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100548416217158515153/100000000000000000000 : ℝ) ≤ (10013450629620547/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (100548416217158515153/100000000000000000000 : ℝ)^2048 ≤ (10013450629620547/10000000000000000 : ℝ)^8333 := by
      have hnat : (100548416217158515153 : ℕ)^2048*10000000000000000^8333 ≤ 10013450629620547^8333*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100548416217158515153 100000000000000000000 10013450629620547 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013450629620547/10000000000000000 : ℝ)) (X := (100548416217158515153/100000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6318552024749425717/6250000000000000000 : ℝ) ≤ (10026901258299151/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (6318552024749425717/6250000000000000000 : ℝ)^2048 ≤ (10026901258299151/10000000000000000 : ℝ)^8333 := by
      have hnat : (6318552024749425717 : ℕ)^2048*10000000000000000^8333 ≤ 10026901258299151^8333*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6318552024749425717 6250000000000000000 10026901258299151 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026901258299151/10000000000000000 : ℝ)) (X := (6318552024749425717/6250000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19163109417/100000000000000000000 : ℝ) ≤ ((137044498705779779779/137050000000000000000 : ℝ)+2*(3362657169651/685250000000000 : ℝ)*(409/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (137044498705779779779/137050000000000000000 : ℝ)+2*(3362657169651/685250000000000 : ℝ)*(409/100000 : ℝ)=(10000000000941943/10000000000000000 : ℝ) by norm_num, show 1+2*(19163109417/100000000000000000000 : ℝ)=(50000000019163109417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(68552024749425717/12500000000000000000 : ℝ)+(19163109417/100000000000000000000 : ℝ) ≤ ((137044498705779779779/137050000000000000000 : ℝ)+(3362657169651/685250000000000 : ℝ)*((27819/100000 : ℝ)+(409/100000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (137044498705779779779/137050000000000000000 : ℝ)+(3362657169651/685250000000000 : ℝ)*((27819/100000 : ℝ)+(409/100000 : ℝ))=(10013450629620547/10000000000000000 : ℝ) by norm_num, show 1+(68552024749425717/12500000000000000000 : ℝ)+(19163109417/100000000000000000000 : ℝ)=(100548416217158515153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(68552024749425717/12500000000000000000 : ℝ) ≤ ((137044498705779779779/137050000000000000000 : ℝ)+2*(3362657169651/685250000000000 : ℝ)*(27819/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (137044498705779779779/137050000000000000000 : ℝ)+2*(3362657169651/685250000000000 : ℝ)*(27819/100000 : ℝ)=(10026901258299151/10000000000000000 : ℝ) by norm_num, show 1+2*(68552024749425717/12500000000000000000 : ℝ)=(6318552024749425717/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137044498705779779779/137050000000000000000 : ℝ)*(X 1 0+X 2 0)+(3362657169651/685250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (409/100000 : ℝ)) (hi := (27819/100000 : ℝ)) (c := (137044498705779779779/137050000000000000000 : ℝ)) (alpha := (3362657169651/685250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137044498705779779779/137050000000000000000 : ℝ)*(X 0 1+X 2 1)+(3362657169651/685250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (409/100000 : ℝ)) (hi := (27819/100000 : ℝ)) (c := (137044498705779779779/137050000000000000000 : ℝ)) (alpha := (3362657169651/685250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137044498705779779779/137050000000000000000 : ℝ)*(X 0 2+X 1 2)+(3362657169651/685250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (409/100000 : ℝ)) (hi := (27819/100000 : ℝ)) (c := (137044498705779779779/137050000000000000000 : ℝ)) (alpha := (3362657169651/685250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1048431767/5000000000 : ℝ)*X 0 0+(1140356069/2000000000 : ℝ)*X 0 1+(200082177/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5419178099/10000000000 : ℝ)*X 1 0+(-2474493753/10000000000 : ℝ)*X 1 1+(4001643/8000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419180021/10000000000 : ℝ)*X 2 0+(125051301/250000000 : ℝ)*X 2 1+(-1237246711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079380503/2500000000 : ℝ)*X 0 0+(183842087/500000000 : ℝ)*X 0 1+(39598849/78125000 : ℝ)*X 0 2+(1079380503/2500000000 : ℝ)*X 1 0+(183842087/500000000 : ℝ)*X 1 1+(39598849/78125000 : ℝ)*X 1 2+(1079380503/2500000000 : ℝ)*X 2 0+(183842087/500000000 : ℝ)*X 2 1+(39598849/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-32776117/156250000 : ℝ)*X 0 0+(5011612091/10000000000 : ℝ)*X 0 1+(5692032973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327486881/625000000 : ℝ)*X 1 0+(-1784514279/10000000000 : ℝ)*X 1 1+(8893801/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239790159/10000000000 : ℝ)*X 2 0+(1423008209/2500000000 : ℝ)*X 2 1+(-111532119/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863825009/2000000000 : ℝ)*X 0 0+(5049642801/10000000000 : ℝ)*X 0 1+(739245749/2000000000 : ℝ)*X 0 2+(863825009/2000000000 : ℝ)*X 1 0+(5049642801/10000000000 : ℝ)*X 1 1+(739245749/2000000000 : ℝ)*X 1 2+(863825009/2000000000 : ℝ)*X 2 0+(5049642801/10000000000 : ℝ)*X 2 1+(739245749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6692134867717700747784507207/1713125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48032367/12500000000000 : ℝ)*(base1) + (455192661/100000000000000 : ℝ)*(base19) + (1017899269/100000000000000 : ℝ)*(base23) + (187208677/100000000000000 : ℝ)*(base37) + (1301013/10000000000000 : ℝ)*(upper3) + (268452252313511/25000000000000 : ℝ)*(major0) + (268452252313511/25000000000000 : ℝ)*(major1) + (268452252313511/25000000000000 : ℝ)*(major2) + (1429130638748887/100000000000000 : ℝ)*(sp0) + (57165148966513/4000000000000 : ℝ)*(sp1) + (1429129848412713/100000000000000 : ℝ)*(sp2) + (718486450515479/100000000000000 : ℝ)*(sp3) + (611822031/100000000000000 : ℝ)*(sp4) + (105434781/6250000000000 : ℝ)*(sp5) + (179621755495773/25000000000000 : ℝ)*(f.failure) + (714565433155991/50000000000000 : ℝ)*(f.sum) + (48367594808119/34262500000000000000000000000 : ℝ)*base65 + (4764166306391505931/3426250000000000000000000000000000 : ℝ)*base68 + (20899805377554005931/3426250000000000000000000000000000 : ℝ)*base70 + (856388697904744069/3426250000000000000000000000000000 : ℝ)*base71 + (8662070472513/68525000000000000000000000000 : ℝ)*base73 + (24846400143219005931/3426250000000000000000000000000000 : ℝ)*base76 + (2986235869952244069/3426250000000000000000000000000000 : ℝ)*base77 + (19965004301196505931/3426250000000000000000000000000000 : ℝ)*base80 + (30921005199881/34262500000000000000000000000 : ℝ)*base82 + (9390719/2500000000000000000000 : ℝ)*base90 + (9390719/2500000000000000000000 : ℝ)*base92 + (9390719/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10151145820369517661362675433/1370500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94625089/100000000000000 : ℝ)*(base1) + (1638081591/100000000000000 : ℝ)*(base19) + (420168193/25000000000000 : ℝ)*(base23) + (38007567/25000000000000 : ℝ)*(upper3) + (33018071/20000000000000 : ℝ)*(upper5) + (276068906317587/25000000000000 : ℝ)*(major0) + (276068906317587/25000000000000 : ℝ)*(major1) + (1104275625270349/100000000000000 : ℝ)*(major2) + (6534239339/100000000000000 : ℝ)*(sp1) + (7262078981/100000000000000 : ℝ)*(sp2) + (73483941169709/5000000000000 : ℝ)*(sp4) + (1469670556448161/100000000000000 : ℝ)*(sp5) + (734834893008669/50000000000000 : ℝ)*(sp6) + (369436090125051/50000000000000 : ℝ)*(sp7) + (73887227487519/10000000000000 : ℝ)*(f.failure) + (1469678728769091/100000000000000 : ℝ)*(f.sum) + (21670348207003/68525000000000000000000000000 : ℝ)*base66 + (19555581304847876727/3426250000000000000000000000000000 : ℝ)*base68 + (86050709370381927129/13705000000000000000000000000000000 : ℝ)*base70 + (8758126263629126727/3426250000000000000000000000000000 : ℝ)*base72 + (183026794052847/68525000000000000000000000000 : ℝ)*base73 + (52968883471131927129/13705000000000000000000000000000000 : ℝ)*base76 + (28581851320319176727/3426250000000000000000000000000000 : ℝ)*base78 + (43592518368515426727/3426250000000000000000000000000000 : ℝ)*base80 + (38982148363163/8565625000000000000000000000 : ℝ)*base82 + (332757/1000000000000000000000 : ℝ)*base90 + (332757/1000000000000000000000 : ℝ)*base92 + (10332757/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1141_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27819/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10221/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_s2_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10750743/50000000 : ℝ)*x 0 + (275550181/500000000 : ℝ)*x 1 + (5158949399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10750743/50000000 : ℝ)^4167 ≤ (3257800326209/25000000000000 : ℝ)^3143 := by
    have hnat : (10750743 : ℕ)^4167*25000000000000^3143 ≤ 3257800326209^3143*50000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10750743 50000000 3257800326209 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275550181/500000000 : ℝ)^4167 ≤ (283663071931/625000000000 : ℝ)^3143 := by
    have hnat : (275550181 : ℕ)^4167*625000000000^3143 ≤ 283663071931^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275550181 500000000 283663071931 625000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5158949399/10000000000 : ℝ)^4167 ≤ (41582707171747/100000000000000 : ℝ)^3143 := by
    have hnat : (5158949399 : ℕ)^4167*100000000000000^3143 ≤ 41582707171747^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158949399 10000000000 41582707171747 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10750743/50000000 : ℝ), (275550181/500000000 : ℝ), (5158949399/10000000000 : ℝ)] ![(3257800326209/25000000000000 : ℝ), (283663071931/625000000000 : ℝ), (41582707171747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10750743/50000000 : ℝ)|^4167 ≤ (3257800326209/25000000000000 : ℝ)^3143
        have hw : |(-10750743/50000000 : ℝ)|=(10750743/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275550181/500000000 : ℝ)|^4167 ≤ (283663071931/625000000000 : ℝ)^3143
        have hw : |(275550181/500000000 : ℝ)|=(275550181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5158949399/10000000000 : ℝ)|^4167 ≤ (41582707171747/100000000000000 : ℝ)^3143
        have hw : |(5158949399/10000000000 : ℝ)|=(5158949399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373908449/10000000000 : ℝ)*x 0 + (-2333189013/10000000000 : ℝ)*x 1 + (5158951413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373908449/10000000000 : ℝ)^4167 ≤ (21947644951813/50000000000000 : ℝ)^3143 := by
    have hnat : (5373908449 : ℕ)^4167*50000000000000^3143 ≤ 21947644951813^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373908449 10000000000 21947644951813 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2333189013/10000000000 : ℝ)^4167 ≤ (7260990694439/50000000000000 : ℝ)^3143 := by
    have hnat : (2333189013 : ℕ)^4167*50000000000000^3143 ≤ 7260990694439^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333189013 10000000000 7260990694439 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5158951413/10000000000 : ℝ)^4167 ≤ (20791364347059/50000000000000 : ℝ)^3143 := by
    have hnat : (5158951413 : ℕ)^4167*50000000000000^3143 ≤ 20791364347059^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158951413 10000000000 20791364347059 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373908449/10000000000 : ℝ), (-2333189013/10000000000 : ℝ), (5158951413/10000000000 : ℝ)] ![(21947644951813/50000000000000 : ℝ), (7260990694439/50000000000000 : ℝ), (20791364347059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373908449/10000000000 : ℝ)|^4167 ≤ (21947644951813/50000000000000 : ℝ)^3143
        have hw : |(5373908449/10000000000 : ℝ)|=(5373908449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2333189013/10000000000 : ℝ)|^4167 ≤ (7260990694439/50000000000000 : ℝ)^3143
        have hw : |(-2333189013/10000000000 : ℝ)|=(2333189013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5158951413/10000000000 : ℝ)|^4167 ≤ (20791364347059/50000000000000 : ℝ)^3143
        have hw : |(5158951413/10000000000 : ℝ)|=(5158951413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373908439/10000000000 : ℝ)*x 0 + (5158951283/10000000000 : ℝ)*x 1 + (-1166594597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373908439/10000000000 : ℝ)^4167 ≤ (43895289795331/100000000000000 : ℝ)^3143 := by
    have hnat : (5373908439 : ℕ)^4167*100000000000000^3143 ≤ 43895289795331^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373908439 10000000000 43895289795331 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158951283/10000000000 : ℝ)^4167 ≤ (5197840913111/12500000000000 : ℝ)^3143 := by
    have hnat : (5158951283 : ℕ)^4167*12500000000000^3143 ≤ 5197840913111^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158951283 10000000000 5197840913111 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166594597/5000000000 : ℝ)^4167 ≤ (580879315299/4000000000000 : ℝ)^3143 := by
    have hnat : (1166594597 : ℕ)^4167*4000000000000^3143 ≤ 580879315299^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166594597 5000000000 580879315299 4000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373908439/10000000000 : ℝ), (5158951283/10000000000 : ℝ), (-1166594597/5000000000 : ℝ)] ![(43895289795331/100000000000000 : ℝ), (5197840913111/12500000000000 : ℝ), (580879315299/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373908439/10000000000 : ℝ)|^4167 ≤ (43895289795331/100000000000000 : ℝ)^3143
        have hw : |(5373908439/10000000000 : ℝ)|=(5373908439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158951283/10000000000 : ℝ)|^4167 ≤ (5197840913111/12500000000000 : ℝ)^3143
        have hw : |(5158951283/10000000000 : ℝ)|=(5158951283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1166594597/5000000000 : ℝ)|^4167 ≤ (580879315299/4000000000000 : ℝ)^3143
        have hw : |(-1166594597/5000000000 : ℝ)|=(1166594597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272129797/625000000 : ℝ)*x 0 + (2008950421/5000000000 : ℝ)*x 1 + (589770193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272129797/625000000 : ℝ)^4167 ≤ (33208342952123/100000000000000 : ℝ)^3143 := by
    have hnat : (272129797 : ℕ)^4167*100000000000000^3143 ≤ 33208342952123^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272129797 625000000 33208342952123 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008950421/5000000000 : ℝ)^4167 ≤ (14926253990787/50000000000000 : ℝ)^3143 := by
    have hnat : (2008950421 : ℕ)^4167*50000000000000^3143 ≤ 14926253990787^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008950421 5000000000 14926253990787 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589770193/1250000000 : ℝ)^4167 ≤ (18469574527737/50000000000000 : ℝ)^3143 := by
    have hnat : (589770193 : ℕ)^4167*50000000000000^3143 ≤ 18469574527737^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589770193 1250000000 18469574527737 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272129797/625000000 : ℝ), (2008950421/5000000000 : ℝ), (589770193/1250000000 : ℝ)] ![(33208342952123/100000000000000 : ℝ), (14926253990787/50000000000000 : ℝ), (18469574527737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272129797/625000000 : ℝ)|^4167 ≤ (33208342952123/100000000000000 : ℝ)^3143
        have hw : |(272129797/625000000 : ℝ)|=(272129797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008950421/5000000000 : ℝ)|^4167 ≤ (14926253990787/50000000000000 : ℝ)^3143
        have hw : |(2008950421/5000000000 : ℝ)|=(2008950421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(589770193/1250000000 : ℝ)|^4167 ≤ (18469574527737/50000000000000 : ℝ)^3143
        have hw : |(589770193/1250000000 : ℝ)|=(589770193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215025153/1000000000 : ℝ)*x 0 + (5161378957/10000000000 : ℝ)*x 1 + (110170993/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215025153/1000000000 : ℝ)^4167 ≤ (13032028371387/100000000000000 : ℝ)^3143 := by
    have hnat : (215025153 : ℕ)^4167*100000000000000^3143 ≤ 13032028371387^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215025153 1000000000 13032028371387 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161378957/10000000000 : ℝ)^4167 ≤ (41608672343247/100000000000000 : ℝ)^3143 := by
    have hnat : (5161378957 : ℕ)^4167*100000000000000^3143 ≤ 41608672343247^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161378957 10000000000 41608672343247 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110170993/200000000 : ℝ)^4167 ≤ (14174781023/31250000000 : ℝ)^3143 := by
    have hnat : (110170993 : ℕ)^4167*31250000000^3143 ≤ 14174781023^3143*200000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110170993 200000000 14174781023 31250000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215025153/1000000000 : ℝ), (5161378957/10000000000 : ℝ), (110170993/200000000 : ℝ)] ![(13032028371387/100000000000000 : ℝ), (41608672343247/100000000000000 : ℝ), (14174781023/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215025153/1000000000 : ℝ)|^4167 ≤ (13032028371387/100000000000000 : ℝ)^3143
        have hw : |(-215025153/1000000000 : ℝ)|=(215025153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161378957/10000000000 : ℝ)|^4167 ≤ (41608672343247/100000000000000 : ℝ)^3143
        have hw : |(5161378957/10000000000 : ℝ)|=(5161378957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110170993/200000000 : ℝ)|^4167 ≤ (14174781023/31250000000 : ℝ)^3143
        have hw : |(110170993/200000000 : ℝ)|=(110170993/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132114723/250000000 : ℝ)*x 0 + (-1983588733/10000000000 : ℝ)*x 1 + (5508550317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132114723/250000000 : ℝ)^4167 ≤ (8586127307643/20000000000000 : ℝ)^3143 := by
    have hnat : (132114723 : ℕ)^4167*20000000000000^3143 ≤ 8586127307643^3143*250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132114723 250000000 8586127307643 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983588733/10000000000 : ℝ)^4167 ≤ (1463757112521/12500000000000 : ℝ)^3143 := by
    have hnat : (1983588733 : ℕ)^4167*12500000000000^3143 ≤ 1463757112521^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983588733 10000000000 1463757112521 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508550317/10000000000 : ℝ)^4167 ≤ (45359306555321/100000000000000 : ℝ)^3143 := by
    have hnat : (5508550317 : ℕ)^4167*100000000000000^3143 ≤ 45359306555321^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508550317 10000000000 45359306555321 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132114723/250000000 : ℝ), (-1983588733/10000000000 : ℝ), (5508550317/10000000000 : ℝ)] ![(8586127307643/20000000000000 : ℝ), (1463757112521/12500000000000 : ℝ), (45359306555321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132114723/250000000 : ℝ)|^4167 ≤ (8586127307643/20000000000000 : ℝ)^3143
        have hw : |(132114723/250000000 : ℝ)|=(132114723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1983588733/10000000000 : ℝ)|^4167 ≤ (1463757112521/12500000000000 : ℝ)^3143
        have hw : |(-1983588733/10000000000 : ℝ)|=(1983588733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508550317/10000000000 : ℝ)|^4167 ≤ (45359306555321/100000000000000 : ℝ)^3143
        have hw : |(5508550317/10000000000 : ℝ)|=(5508550317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056917487/2000000000 : ℝ)*x 0 + (1101710023/2000000000 : ℝ)*x 1 + (-123974441/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056917487/2000000000 : ℝ)^4167 ≤ (21465310272023/50000000000000 : ℝ)^3143 := by
    have hnat : (1056917487 : ℕ)^4167*50000000000000^3143 ≤ 21465310272023^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056917487 2000000000 21465310272023 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101710023/2000000000 : ℝ)^4167 ≤ (22679652175031/50000000000000 : ℝ)^3143 := by
    have hnat : (1101710023 : ℕ)^4167*50000000000000^3143 ≤ 22679652175031^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101710023 2000000000 22679652175031 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123974441/625000000 : ℝ)^4167 ≤ (11710075081923/100000000000000 : ℝ)^3143 := by
    have hnat : (123974441 : ℕ)^4167*100000000000000^3143 ≤ 11710075081923^3143*625000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123974441 625000000 11710075081923 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056917487/2000000000 : ℝ), (1101710023/2000000000 : ℝ), (-123974441/625000000 : ℝ)] ![(21465310272023/50000000000000 : ℝ), (22679652175031/50000000000000 : ℝ), (11710075081923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056917487/2000000000 : ℝ)|^4167 ≤ (21465310272023/50000000000000 : ℝ)^3143
        have hw : |(1056917487/2000000000 : ℝ)|=(1056917487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101710023/2000000000 : ℝ)|^4167 ≤ (22679652175031/50000000000000 : ℝ)^3143
        have hw : |(1101710023/2000000000 : ℝ)|=(1101710023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123974441/625000000 : ℝ)|^4167 ≤ (11710075081923/100000000000000 : ℝ)^3143
        have hw : |(-123974441/625000000 : ℝ)|=(123974441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s2_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177140317/5000000000 : ℝ)*x 0 + (471333067/1000000000 : ℝ)*x 1 + (4022780209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177140317/5000000000 : ℝ)^4167 ≤ (1328416183611/4000000000000 : ℝ)^3143 := by
    have hnat : (2177140317 : ℕ)^4167*4000000000000^3143 ≤ 1328416183611^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177140317 5000000000 1328416183611 4000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471333067/1000000000 : ℝ)^4167 ≤ (18444506714289/50000000000000 : ℝ)^3143 := by
    have hnat : (471333067 : ℕ)^4167*50000000000000^3143 ≤ 18444506714289^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471333067 1000000000 18444506714289 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022780209/10000000000 : ℝ)^4167 ≤ (74751454909/250000000000 : ℝ)^3143 := by
    have hnat : (4022780209 : ℕ)^4167*250000000000^3143 ≤ 74751454909^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022780209 10000000000 74751454909 250000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177140317/5000000000 : ℝ), (471333067/1000000000 : ℝ), (4022780209/10000000000 : ℝ)] ![(1328416183611/4000000000000 : ℝ), (18444506714289/50000000000000 : ℝ), (74751454909/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177140317/5000000000 : ℝ)|^4167 ≤ (1328416183611/4000000000000 : ℝ)^3143
        have hw : |(2177140317/5000000000 : ℝ)|=(2177140317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(471333067/1000000000 : ℝ)|^4167 ≤ (18444506714289/50000000000000 : ℝ)^3143
        have hw : |(471333067/1000000000 : ℝ)|=(471333067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022780209/10000000000 : ℝ)|^4167 ≤ (74751454909/250000000000 : ℝ)^3143
        have hw : |(4022780209/10000000000 : ℝ)|=(4022780209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10221/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4533/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8253/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10221/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10221/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10221/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10221/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10221/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10221/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1411/25000 : ℝ) ^ (8333/2048 : ℝ) ≤ (832525819957361/100000000000000000000 : ℝ) := by
    have hpowers : (1411/25000 : ℝ)^8333 ≤ (832525819957361/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1411 : ℕ)^8333*100000000000000000000^2048 ≤ 832525819957361^2048*25000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 25000 832525819957361 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/25000 : ℝ)) (X := (832525819957361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10221/50000 : ℝ) ^ (8333/2048 : ℝ) ≤ (31307953665919677/20000000000000000000 : ℝ) := by
    have hpowers : (10221/50000 : ℝ)^8333 ≤ (31307953665919677/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10221 : ℕ)^8333*20000000000000000000^2048 ≤ 31307953665919677^2048*50000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10221 50000 31307953665919677 20000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10221/50000 : ℝ)) (X := (31307953665919677/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000832525819957361/50000000000000000000 : ℝ) ≤ (2500010230422257/2500000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50000832525819957361/50000000000000000000 : ℝ)^2048 ≤ (2500010230422257/2500000000000000 : ℝ)^8333 := by
      have hnat : (50000832525819957361 : ℕ)^2048*2500000000000000^8333 ≤ 2500010230422257^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000832525819957361 50000000000000000000 2500010230422257 2500000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010230422257/2500000000000000 : ℝ)) (X := (50000832525819957361/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50078686147074777873/50000000000000000000 : ℝ) ≤ (5001932721458517/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50078686147074777873/50000000000000000000 : ℝ)^2048 ≤ (5001932721458517/5000000000000000 : ℝ)^8333 := by
      have hnat : (50078686147074777873 : ℕ)^2048*5000000000000000^8333 ≤ 5001932721458517^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078686147074777873 50000000000000000000 5001932721458517 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001932721458517/5000000000000000 : ℝ)) (X := (50078686147074777873/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10031307953665919677/10000000000000000000 : ℝ) ≤ (125096124551813/125000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (10031307953665919677/10000000000000000000 : ℝ)^2048 ≤ (125096124551813/125000000000000 : ℝ)^8333 := by
      have hnat : (10031307953665919677 : ℕ)^2048*125000000000000^8333 ≤ 125096124551813^8333*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10031307953665919677 10000000000000000000 125096124551813 125000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125096124551813/125000000000000 : ℝ)) (X := (10031307953665919677/10000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(832525819957361/100000000000000000000 : ℝ) ≤ ((18492179295441563077/18497500000000000000 : ℝ)+2*(1912260614003/739900000000000 : ℝ)*(1411/25000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (18492179295441563077/18497500000000000000 : ℝ)+2*(1912260614003/739900000000000 : ℝ)*(1411/25000 : ℝ)=(2500010230422257/2500000000000000 : ℝ) by norm_num, show 1+2*(832525819957361/100000000000000000000 : ℝ)=(50000832525819957361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31307953665919677/20000000000000000000 : ℝ)+(832525819957361/100000000000000000000 : ℝ) ≤ ((18492179295441563077/18497500000000000000 : ℝ)+(1912260614003/739900000000000 : ℝ)*((10221/50000 : ℝ)+(1411/25000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (18492179295441563077/18497500000000000000 : ℝ)+(1912260614003/739900000000000 : ℝ)*((10221/50000 : ℝ)+(1411/25000 : ℝ))=(5001932721458517/5000000000000000 : ℝ) by norm_num, show 1+(31307953665919677/20000000000000000000 : ℝ)+(832525819957361/100000000000000000000 : ℝ)=(50078686147074777873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31307953665919677/20000000000000000000 : ℝ) ≤ ((18492179295441563077/18497500000000000000 : ℝ)+2*(1912260614003/739900000000000 : ℝ)*(10221/50000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (18492179295441563077/18497500000000000000 : ℝ)+2*(1912260614003/739900000000000 : ℝ)*(10221/50000 : ℝ)=(125096124551813/125000000000000 : ℝ) by norm_num, show 1+2*(31307953665919677/20000000000000000000 : ℝ)=(10031307953665919677/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18492179295441563077/18497500000000000000 : ℝ)*(X 1 0+X 2 0)+(1912260614003/739900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1411/25000 : ℝ)) (hi := (10221/50000 : ℝ)) (c := (18492179295441563077/18497500000000000000 : ℝ)) (alpha := (1912260614003/739900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18492179295441563077/18497500000000000000 : ℝ)*(X 0 1+X 2 1)+(1912260614003/739900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1411/25000 : ℝ)) (hi := (10221/50000 : ℝ)) (c := (18492179295441563077/18497500000000000000 : ℝ)) (alpha := (1912260614003/739900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18492179295441563077/18497500000000000000 : ℝ)*(X 0 2+X 1 2)+(1912260614003/739900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1411/25000 : ℝ)) (hi := (10221/50000 : ℝ)) (c := (18492179295441563077/18497500000000000000 : ℝ)) (alpha := (1912260614003/739900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10750743/50000000 : ℝ)*X 0 0+(275550181/500000000 : ℝ)*X 0 1+(5158949399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373908449/10000000000 : ℝ)*X 1 0+(-2333189013/10000000000 : ℝ)*X 1 1+(5158951413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373908439/10000000000 : ℝ)*X 2 0+(5158951283/10000000000 : ℝ)*X 2 1+(-1166594597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272129797/625000000 : ℝ)*X 0 0+(2008950421/5000000000 : ℝ)*X 0 1+(589770193/1250000000 : ℝ)*X 0 2+(272129797/625000000 : ℝ)*X 1 0+(2008950421/5000000000 : ℝ)*X 1 1+(589770193/1250000000 : ℝ)*X 1 2+(272129797/625000000 : ℝ)*X 2 0+(2008950421/5000000000 : ℝ)*X 2 1+(589770193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215025153/1000000000 : ℝ)*X 0 0+(5161378957/10000000000 : ℝ)*X 0 1+(110170993/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132114723/250000000 : ℝ)*X 1 0+(-1983588733/10000000000 : ℝ)*X 1 1+(5508550317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056917487/2000000000 : ℝ)*X 2 0+(1101710023/2000000000 : ℝ)*X 2 1+(-123974441/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177140317/5000000000 : ℝ)*X 0 0+(471333067/1000000000 : ℝ)*X 0 1+(4022780209/10000000000 : ℝ)*X 0 2+(2177140317/5000000000 : ℝ)*X 1 0+(471333067/1000000000 : ℝ)*X 1 1+(4022780209/10000000000 : ℝ)*X 1 2+(2177140317/5000000000 : ℝ)*X 2 0+(471333067/1000000000 : ℝ)*X 2 1+(4022780209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3220620406399518428261557083/924875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89305417/100000000000000 : ℝ)*(base15) + (66367771/100000000000000 : ℝ)*(base29) + (66564487/50000000000000 : ℝ)*(upper2) + (22665801/25000000000000 : ℝ)*(upper3) + (88974973/100000000000000 : ℝ)*(upper4) + (133391878770673/6250000000000 : ℝ)*(major0) + (2134270126698539/100000000000000 : ℝ)*(major1) + (2134270126698539/100000000000000 : ℝ)*(major2) + (1420242853638797/50000000000000 : ℝ)*(sp0) + (568099405933729/20000000000000 : ℝ)*(sp1) + (1420248559487031/50000000000000 : ℝ)*(sp2) + (714020561353069/50000000000000 : ℝ)*(sp3) + (11478064239/100000000000000 : ℝ)*(sp4) + (914637511/50000000000000 : ℝ)*(sp7) + (35701073799529/2500000000000 : ℝ)*(f.failure) + (2840497185341833/100000000000000 : ℝ)*(f.sum) + (207796295461887/36995000000000000000000000000 : ℝ)*base65 + (1428567781107419503/1849750000000000000000000000000000 : ℝ)*base67 + (5452833776929169503/1849750000000000000000000000000000 : ℝ)*base69 + (1103585810534816017/231218750000000000000000000000000 : ℝ)*base71 + (33111703109633/10570000000000000000000000000 : ℝ)*base73 + (2618004310896405497/1849750000000000000000000000000000 : ℝ)*base76 + (232347175891472267/231218750000000000000000000000000 : ℝ)*base77 + (10893730542260344503/1849750000000000000000000000000000 : ℝ)*base79 + (8614511597763/10570000000000000000000000000 : ℝ)*base81 + (1826787/250000000000000000000 : ℝ)*base90 + (1826787/250000000000000000000 : ℝ)*base92 + (1826787/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10599718312663199143683515967/924875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83138911/4000000000000 : ℝ)*(base19) + (1507096633/100000000000000 : ℝ)*(base23) + (292036101/100000000000000 : ℝ)*(upper2) + (146907537/100000000000000 : ℝ)*(upper3) + (164202663/50000000000000 : ℝ)*(upper5) + (2164269481298619/100000000000000 : ℝ)*(major0) + (2164269481298619/100000000000000 : ℝ)*(major1) + (2164269481298619/100000000000000 : ℝ)*(major2) + (27996434089/100000000000000 : ℝ)*(sp1) + (9384189367/100000000000000 : ℝ)*(sp2) + (1440211510464681/50000000000000 : ℝ)*(sp4) + (1440196473011249/50000000000000 : ℝ)*(sp5) + (1440206064821681/50000000000000 : ℝ)*(sp6) + (1448115559644417/100000000000000 : ℝ)*(sp7) + (1448115559644417/100000000000000 : ℝ)*(f.failure) + (1440211510464681/50000000000000 : ℝ)*(f.sum) + (193239400721553/36995000000000000000000000000 : ℝ)*base66 + (3751539756986084337/1849750000000000000000000000000000 : ℝ)*base68 + (8088392630228834337/1849750000000000000000000000000000 : ℝ)*base70 + (5358150616817334337/1849750000000000000000000000000000 : ℝ)*base72 + (19663638362537/9248750000000000000000000000 : ℝ)*base74 + (4268892546198084337/1849750000000000000000000000000000 : ℝ)*base76 + (6470746500401834337/1849750000000000000000000000000000 : ℝ)*base78 + (7161478147671834337/1849750000000000000000000000000000 : ℝ)*base80 + (9484515837/144511718750000000000000000 : ℝ)*base81 + (48268149/10000000000000000000000 : ℝ)*base89 + (48268149/10000000000000000000000 : ℝ)*base91 + (48268149/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1141_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10221/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1141_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1141_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1141_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1141_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

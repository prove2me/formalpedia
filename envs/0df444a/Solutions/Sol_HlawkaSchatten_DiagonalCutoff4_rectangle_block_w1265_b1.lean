-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1265_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:56:50.591635+00:00
-- url     : https://prove2.me/submissions/aa6b0544-8d4b-441d-9657-690879943da4

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
theorem support_rectangle_w1265_s3_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053377881/5000000000 : ℝ)*x 0 + (5417678761/10000000000 : ℝ)*x 1 + (5242350311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053377881/5000000000 : ℝ)^4229 ≤ (800549911721/6250000000000 : ℝ)^3205 := by
    have hnat : (1053377881 : ℕ)^4229*6250000000000^3205 ≤ 800549911721^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053377881 5000000000 800549911721 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417678761/10000000000 : ℝ)^4229 ≤ (22270828843347/50000000000000 : ℝ)^3205 := by
    have hnat : (5417678761 : ℕ)^4229*50000000000000^3205 ≤ 22270828843347^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417678761 10000000000 22270828843347 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242350311/10000000000 : ℝ)^4229 ≤ (852990874023/2000000000000 : ℝ)^3205 := by
    have hnat : (5242350311 : ℕ)^4229*2000000000000^3205 ≤ 852990874023^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242350311 10000000000 852990874023 2000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053377881/5000000000 : ℝ), (5417678761/10000000000 : ℝ), (5242350311/10000000000 : ℝ)] ![(800549911721/6250000000000 : ℝ), (22270828843347/50000000000000 : ℝ), (852990874023/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053377881/5000000000 : ℝ)|^4229 ≤ (800549911721/6250000000000 : ℝ)^3205
        have hw : |(-1053377881/5000000000 : ℝ)|=(1053377881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417678761/10000000000 : ℝ)|^4229 ≤ (22270828843347/50000000000000 : ℝ)^3205
        have hw : |(5417678761/10000000000 : ℝ)|=(5417678761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242350311/10000000000 : ℝ)|^4229 ≤ (852990874023/2000000000000 : ℝ)^3205
        have hw : |(5242350311/10000000000 : ℝ)|=(5242350311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350987731/10000000000 : ℝ)*x 0 + (-68630023/312500000 : ℝ)*x 1 + (209694017/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350987731/10000000000 : ℝ)^4229 ≤ (8763919661081/20000000000000 : ℝ)^3205 := by
    have hnat : (5350987731 : ℕ)^4229*20000000000000^3205 ≤ 8763919661081^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350987731 10000000000 8763919661081 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68630023/312500000 : ℝ)^4229 ≤ (13530856756993/100000000000000 : ℝ)^3205 := by
    have hnat : (68630023 : ℕ)^4229*100000000000000^3205 ≤ 13530856756993^3205*312500000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68630023 312500000 13530856756993 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209694017/400000000 : ℝ)^4229 ≤ (42649544924929/100000000000000 : ℝ)^3205 := by
    have hnat : (209694017 : ℕ)^4229*100000000000000^3205 ≤ 42649544924929^3205*400000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209694017 400000000 42649544924929 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350987731/10000000000 : ℝ), (-68630023/312500000 : ℝ), (209694017/400000000 : ℝ)] ![(8763919661081/20000000000000 : ℝ), (13530856756993/100000000000000 : ℝ), (42649544924929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350987731/10000000000 : ℝ)|^4229 ≤ (8763919661081/20000000000000 : ℝ)^3205
        have hw : |(5350987731/10000000000 : ℝ)|=(5350987731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68630023/312500000 : ℝ)|^4229 ≤ (13530856756993/100000000000000 : ℝ)^3205
        have hw : |(-68630023/312500000 : ℝ)|=(68630023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209694017/400000000 : ℝ)|^4229 ≤ (42649544924929/100000000000000 : ℝ)^3205
        have hw : |(209694017/400000000 : ℝ)|=(209694017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337746929/2500000000 : ℝ)*x 0 + (327646931/625000000 : ℝ)*x 1 + (-2196160133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337746929/2500000000 : ℝ)^4229 ≤ (21909799071661/50000000000000 : ℝ)^3205 := by
    have hnat : (1337746929 : ℕ)^4229*50000000000000^3205 ≤ 21909799071661^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337746929 2500000000 21909799071661 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327646931/625000000 : ℝ)^4229 ≤ (42649549981067/100000000000000 : ℝ)^3205 := by
    have hnat : (327646931 : ℕ)^4229*100000000000000^3205 ≤ 42649549981067^3205*625000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327646931 625000000 42649549981067 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196160133/10000000000 : ℝ)^4229 ≤ (6765425927413/50000000000000 : ℝ)^3205 := by
    have hnat : (2196160133 : ℕ)^4229*50000000000000^3205 ≤ 6765425927413^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196160133 10000000000 6765425927413 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337746929/2500000000 : ℝ), (327646931/625000000 : ℝ), (-2196160133/10000000000 : ℝ)] ![(21909799071661/50000000000000 : ℝ), (42649549981067/100000000000000 : ℝ), (6765425927413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337746929/2500000000 : ℝ)|^4229 ≤ (21909799071661/50000000000000 : ℝ)^3205
        have hw : |(1337746929/2500000000 : ℝ)|=(1337746929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327646931/625000000 : ℝ)|^4229 ≤ (42649549981067/100000000000000 : ℝ)^3205
        have hw : |(327646931/625000000 : ℝ)|=(327646931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196160133/10000000000 : ℝ)|^4229 ≤ (6765425927413/50000000000000 : ℝ)^3205
        have hw : |(-2196160133/10000000000 : ℝ)|=(2196160133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173018891/5000000000 : ℝ)*x 0 + (2085481077/5000000000 : ℝ)*x 1 + (905641331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173018891/5000000000 : ℝ)^4229 ≤ (16650761187111/50000000000000 : ℝ)^3205 := by
    have hnat : (2173018891 : ℕ)^4229*50000000000000^3205 ≤ 16650761187111^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173018891 5000000000 16650761187111 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085481077/5000000000 : ℝ)^4229 ≤ (31542886599089/100000000000000 : ℝ)^3205 := by
    have hnat : (2085481077 : ℕ)^4229*100000000000000^3205 ≤ 31542886599089^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085481077 5000000000 31542886599089 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905641331/2000000000 : ℝ)^4229 ≤ (35155591020919/100000000000000 : ℝ)^3205 := by
    have hnat : (905641331 : ℕ)^4229*100000000000000^3205 ≤ 35155591020919^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905641331 2000000000 35155591020919 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173018891/5000000000 : ℝ), (2085481077/5000000000 : ℝ), (905641331/2000000000 : ℝ)] ![(16650761187111/50000000000000 : ℝ), (31542886599089/100000000000000 : ℝ), (35155591020919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173018891/5000000000 : ℝ)|^4229 ≤ (16650761187111/50000000000000 : ℝ)^3205
        have hw : |(2173018891/5000000000 : ℝ)|=(2173018891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085481077/5000000000 : ℝ)|^4229 ≤ (31542886599089/100000000000000 : ℝ)^3205
        have hw : |(2085481077/5000000000 : ℝ)|=(2085481077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(905641331/2000000000 : ℝ)|^4229 ≤ (35155591020919/100000000000000 : ℝ)^3205
        have hw : |(905641331/2000000000 : ℝ)|=(905641331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106769671/10000000000 : ℝ)*x 0 + (262148929/500000000 : ℝ)*x 1 + (5417046753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106769671/10000000000 : ℝ)^4229 ≤ (6404455085549/50000000000000 : ℝ)^3205 := by
    have hnat : (2106769671 : ℕ)^4229*50000000000000^3205 ≤ 6404455085549^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106769671 10000000000 6404455085549 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262148929/500000000 : ℝ)^4229 ≤ (21328144117569/50000000000000 : ℝ)^3205 := by
    have hnat : (262148929 : ℕ)^4229*50000000000000^3205 ≤ 21328144117569^3205*500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262148929 500000000 21328144117569 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417046753/10000000000 : ℝ)^4229 ≤ (4453480158487/10000000000000 : ℝ)^3205 := by
    have hnat : (5417046753 : ℕ)^4229*10000000000000^3205 ≤ 4453480158487^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417046753 10000000000 4453480158487 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106769671/10000000000 : ℝ), (262148929/500000000 : ℝ), (5417046753/10000000000 : ℝ)] ![(6404455085549/50000000000000 : ℝ), (21328144117569/50000000000000 : ℝ), (4453480158487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106769671/10000000000 : ℝ)|^4229 ≤ (6404455085549/50000000000000 : ℝ)^3205
        have hw : |(-2106769671/10000000000 : ℝ)|=(2106769671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262148929/500000000 : ℝ)|^4229 ≤ (21328144117569/50000000000000 : ℝ)^3205
        have hw : |(262148929/500000000 : ℝ)|=(262148929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417046753/10000000000 : ℝ)|^4229 ≤ (4453480158487/10000000000000 : ℝ)^3205
        have hw : |(5417046753/10000000000 : ℝ)|=(5417046753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2653094781/5000000000 : ℝ)*x 0 + (-20214637/100000000 : ℝ)*x 1 + (541704659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653094781/5000000000 : ℝ)^4229 ≤ (10834045298189/25000000000000 : ℝ)^3205 := by
    have hnat : (2653094781 : ℕ)^4229*25000000000000^3205 ≤ 10834045298189^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653094781 5000000000 10834045298189 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20214637/100000000 : ℝ)^4229 ≤ (3032254743567/25000000000000 : ℝ)^3205 := by
    have hnat : (20214637 : ℕ)^4229*25000000000000^3205 ≤ 3032254743567^3205*100000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20214637 100000000 3032254743567 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541704659/1000000000 : ℝ)^4229 ≤ (22267399908329/50000000000000 : ℝ)^3205 := by
    have hnat : (541704659 : ℕ)^4229*50000000000000^3205 ≤ 22267399908329^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541704659 1000000000 22267399908329 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653094781/5000000000 : ℝ), (-20214637/100000000 : ℝ), (541704659/1000000000 : ℝ)] ![(10834045298189/25000000000000 : ℝ), (3032254743567/25000000000000 : ℝ), (22267399908329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653094781/5000000000 : ℝ)|^4229 ≤ (10834045298189/25000000000000 : ℝ)^3205
        have hw : |(2653094781/5000000000 : ℝ)|=(2653094781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20214637/100000000 : ℝ)|^4229 ≤ (3032254743567/25000000000000 : ℝ)^3205
        have hw : |(-20214637/100000000 : ℝ)|=(20214637/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541704659/1000000000 : ℝ)|^4229 ≤ (22267399908329/50000000000000 : ℝ)^3205
        have hw : |(541704659/1000000000 : ℝ)|=(541704659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2653094443/5000000000 : ℝ)*x 0 + (2708523517/5000000000 : ℝ)*x 1 + (-505366003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653094443/5000000000 : ℝ)^4229 ≤ (8667234781569/20000000000000 : ℝ)^3205 := by
    have hnat : (2653094443 : ℕ)^4229*20000000000000^3205 ≤ 8667234781569^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653094443 5000000000 8667234781569 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708523517/5000000000 : ℝ)^4229 ≤ (2783425289571/6250000000000 : ℝ)^3205 := by
    have hnat : (2708523517 : ℕ)^4229*6250000000000^3205 ≤ 2783425289571^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708523517 5000000000 2783425289571 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505366003/2500000000 : ℝ)^4229 ≤ (6064510722211/50000000000000 : ℝ)^3205 := by
    have hnat : (505366003 : ℕ)^4229*50000000000000^3205 ≤ 6064510722211^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505366003 2500000000 6064510722211 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653094443/5000000000 : ℝ), (2708523517/5000000000 : ℝ), (-505366003/2500000000 : ℝ)] ![(8667234781569/20000000000000 : ℝ), (2783425289571/6250000000000 : ℝ), (6064510722211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653094443/5000000000 : ℝ)|^4229 ≤ (8667234781569/20000000000000 : ℝ)^3205
        have hw : |(2653094443/5000000000 : ℝ)|=(2653094443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708523517/5000000000 : ℝ)|^4229 ≤ (2783425289571/6250000000000 : ℝ)^3205
        have hw : |(2708523517/5000000000 : ℝ)|=(2708523517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505366003/2500000000 : ℝ)|^4229 ≤ (6064510722211/50000000000000 : ℝ)^3205
        have hw : |(-505366003/2500000000 : ℝ)|=(505366003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173032729/5000000000 : ℝ)*x 0 + (1131731431/2500000000 : ℝ)*x 1 + (4172248997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173032729/5000000000 : ℝ)^4229 ≤ (16650901098803/50000000000000 : ℝ)^3205 := by
    have hnat : (2173032729 : ℕ)^4229*50000000000000^3205 ≤ 16650901098803^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173032729 5000000000 16650901098803 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131731431/2500000000 : ℝ)^4229 ≤ (1757123475381/5000000000000 : ℝ)^3205 := by
    have hnat : (1131731431 : ℕ)^4229*5000000000000^3205 ≤ 1757123475381^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131731431 2500000000 1757123475381 5000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172248997/10000000000 : ℝ)^4229 ≤ (31555728277923/100000000000000 : ℝ)^3205 := by
    have hnat : (4172248997 : ℕ)^4229*100000000000000^3205 ≤ 31555728277923^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172248997 10000000000 31555728277923 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173032729/5000000000 : ℝ), (1131731431/2500000000 : ℝ), (4172248997/10000000000 : ℝ)] ![(16650901098803/50000000000000 : ℝ), (1757123475381/5000000000000 : ℝ), (31555728277923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173032729/5000000000 : ℝ)|^4229 ≤ (16650901098803/50000000000000 : ℝ)^3205
        have hw : |(2173032729/5000000000 : ℝ)|=(2173032729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131731431/2500000000 : ℝ)|^4229 ≤ (1757123475381/5000000000000 : ℝ)^3205
        have hw : |(1131731431/2500000000 : ℝ)|=(1131731431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172248997/10000000000 : ℝ)|^4229 ≤ (31555728277923/100000000000000 : ℝ)^3205
        have hw : |(4172248997/10000000000 : ℝ)|=(4172248997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_8 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-90745997/10000000000 : ℝ)*x 0 + (2952329841/5000000000 : ℝ)*x 1 + (1180933529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90745997/10000000000 : ℝ)^4229 ≤ (202000182701/100000000000000 : ℝ)^3205 := by
    have hnat : (90745997 : ℕ)^4229*100000000000000^3205 ≤ 202000182701^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90745997 10000000000 202000182701 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2952329841/5000000000 : ℝ)^4229 ≤ (49898955505891/100000000000000 : ℝ)^3205 := by
    have hnat : (2952329841 : ℕ)^4229*100000000000000^3205 ≤ 49898955505891^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2952329841 5000000000 49898955505891 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180933529/2000000000 : ℝ)^4229 ≤ (49899044299773/100000000000000 : ℝ)^3205 := by
    have hnat : (1180933529 : ℕ)^4229*100000000000000^3205 ≤ 49899044299773^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180933529 2000000000 49899044299773 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90745997/10000000000 : ℝ), (2952329841/5000000000 : ℝ), (1180933529/2000000000 : ℝ)] ![(202000182701/100000000000000 : ℝ), (49898955505891/100000000000000 : ℝ), (49899044299773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90745997/10000000000 : ℝ)|^4229 ≤ (202000182701/100000000000000 : ℝ)^3205
        have hw : |(-90745997/10000000000 : ℝ)|=(90745997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2952329841/5000000000 : ℝ)|^4229 ≤ (49898955505891/100000000000000 : ℝ)^3205
        have hw : |(2952329841/5000000000 : ℝ)|=(2952329841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1180933529/2000000000 : ℝ)|^4229 ≤ (49899044299773/100000000000000 : ℝ)^3205
        have hw : |(1180933529/2000000000 : ℝ)|=(1180933529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_9 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (979873279/10000000000 : ℝ)*x 0 + (-87462423/200000000 : ℝ)*x 1 + (3470178461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979873279/10000000000 : ℝ)^4229 ≤ (4664959906469/100000000000000 : ℝ)^3205 := by
    have hnat : (979873279 : ℕ)^4229*100000000000000^3205 ≤ 4664959906469^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979873279 10000000000 4664959906469 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87462423/200000000 : ℝ)^4229 ≤ (1343025031363/4000000000000 : ℝ)^3205 := by
    have hnat : (87462423 : ℕ)^4229*4000000000000^3205 ≤ 1343025031363^3205*200000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87462423 200000000 1343025031363 4000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3470178461/5000000000 : ℝ)^4229 ≤ (15439853573491/25000000000000 : ℝ)^3205 := by
    have hnat : (3470178461 : ℕ)^4229*25000000000000^3205 ≤ 15439853573491^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470178461 5000000000 15439853573491 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(979873279/10000000000 : ℝ), (-87462423/200000000 : ℝ), (3470178461/5000000000 : ℝ)] ![(4664959906469/100000000000000 : ℝ), (1343025031363/4000000000000 : ℝ), (15439853573491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(979873279/10000000000 : ℝ)|^4229 ≤ (4664959906469/100000000000000 : ℝ)^3205
        have hw : |(979873279/10000000000 : ℝ)|=(979873279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87462423/200000000 : ℝ)|^4229 ≤ (1343025031363/4000000000000 : ℝ)^3205
        have hw : |(-87462423/200000000 : ℝ)|=(87462423/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3470178461/5000000000 : ℝ)|^4229 ≤ (15439853573491/25000000000000 : ℝ)^3205
        have hw : |(3470178461/5000000000 : ℝ)|=(3470178461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s3_10 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (24496609/250000000 : ℝ)*x 0 + (6940336849/10000000000 : ℝ)*x 1 + (-874629989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24496609/250000000 : ℝ)^4229 ≤ (4664903878719/100000000000000 : ℝ)^3205 := by
    have hnat : (24496609 : ℕ)^4229*100000000000000^3205 ≤ 4664903878719^3205*250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24496609 250000000 4664903878719 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6940336849/10000000000 : ℝ)^4229 ≤ (6175917860291/10000000000000 : ℝ)^3205 := by
    have hnat : (6940336849 : ℕ)^4229*10000000000000^3205 ≤ 6175917860291^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6940336849 10000000000 6175917860291 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874629989/2000000000 : ℝ)^4229 ≤ (33575917499771/100000000000000 : ℝ)^3205 := by
    have hnat : (874629989 : ℕ)^4229*100000000000000^3205 ≤ 33575917499771^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874629989 2000000000 33575917499771 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24496609/250000000 : ℝ), (6940336849/10000000000 : ℝ), (-874629989/2000000000 : ℝ)] ![(4664903878719/100000000000000 : ℝ), (6175917860291/10000000000000 : ℝ), (33575917499771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24496609/250000000 : ℝ)|^4229 ≤ (4664903878719/100000000000000 : ℝ)^3205
        have hw : |(24496609/250000000 : ℝ)|=(24496609/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6940336849/10000000000 : ℝ)|^4229 ≤ (6175917860291/10000000000000 : ℝ)^3205
        have hw : |(6940336849/10000000000 : ℝ)|=(6940336849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-874629989/2000000000 : ℝ)|^4229 ≤ (33575917499771/100000000000000 : ℝ)^3205
        have hw : |(-874629989/2000000000 : ℝ)|=(874629989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10969/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (367/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4041/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1199/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4041/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1199/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4041/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1199/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4041/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1199/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4041/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1199/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4041/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1199/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1199/12500 : ℝ) ^ (8457/2048 : ℝ) ≤ (1250061242530073/20000000000000000000 : ℝ) := by
    have hpowers : (1199/12500 : ℝ)^8457 ≤ (1250061242530073/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1199 : ℕ)^8457*20000000000000000000^2048 ≤ 1250061242530073^2048*12500^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1199 12500 1250061242530073 20000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1199/12500 : ℝ)) (X := (1250061242530073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4041/25000 : ℝ) ^ (8457/2048 : ℝ) ≤ (53924473743693417/100000000000000000000 : ℝ) := by
    have hpowers : (4041/25000 : ℝ)^8457 ≤ (53924473743693417/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4041 : ℕ)^8457*100000000000000000000^2048 ≤ 53924473743693417^2048*25000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4041 25000 53924473743693417 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4041/25000 : ℝ)) (X := (53924473743693417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001250061242530073/10000000000000000000 : ℝ) ≤ (10000302708308893/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (10001250061242530073/10000000000000000000 : ℝ)^2048 ≤ (10000302708308893/10000000000000000 : ℝ)^8457 := by
      have hnat : (10001250061242530073 : ℕ)^2048*10000000000000000^8457 ≤ 10000302708308893^8457*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001250061242530073 10000000000000000000 10000302708308893 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000302708308893/10000000000000000 : ℝ)) (X := (10001250061242530073/10000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50030087389978171891/50000000000000000000 : ℝ) ≤ (10001456897948141/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50030087389978171891/50000000000000000000 : ℝ)^2048 ≤ (10001456897948141/10000000000000000 : ℝ)^8457 := by
      have hnat : (50030087389978171891 : ℕ)^2048*10000000000000000^8457 ≤ 10001456897948141^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030087389978171891 50000000000000000000 10001456897948141 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001456897948141/10000000000000000 : ℝ)) (X := (50030087389978171891/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50053924473743693417/50000000000000000000 : ℝ) ≤ (10002611087587389/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50053924473743693417/50000000000000000000 : ℝ)^2048 ≤ (10002611087587389/10000000000000000 : ℝ)^8457 := by
      have hnat : (50053924473743693417 : ℕ)^2048*10000000000000000^8457 ≤ 10002611087587389^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053924473743693417 50000000000000000000 10002611087587389 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002611087587389/10000000000000000 : ℝ)) (X := (50053924473743693417/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1250061242530073/20000000000000000000 : ℝ) ≤ ((16424961856241677791/16430000000000000000 : ℝ)+2*(72136852453/41075000000000 : ℝ)*(1199/12500 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (16424961856241677791/16430000000000000000 : ℝ)+2*(72136852453/41075000000000 : ℝ)*(1199/12500 : ℝ)=(10000302708308893/10000000000000000 : ℝ) by norm_num, show 1+2*(1250061242530073/20000000000000000000 : ℝ)=(10001250061242530073/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53924473743693417/100000000000000000000 : ℝ)+(1250061242530073/20000000000000000000 : ℝ) ≤ ((16424961856241677791/16430000000000000000 : ℝ)+(72136852453/41075000000000 : ℝ)*((4041/25000 : ℝ)+(1199/12500 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (16424961856241677791/16430000000000000000 : ℝ)+(72136852453/41075000000000 : ℝ)*((4041/25000 : ℝ)+(1199/12500 : ℝ))=(10001456897948141/10000000000000000 : ℝ) by norm_num, show 1+(53924473743693417/100000000000000000000 : ℝ)+(1250061242530073/20000000000000000000 : ℝ)=(50030087389978171891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53924473743693417/100000000000000000000 : ℝ) ≤ ((16424961856241677791/16430000000000000000 : ℝ)+2*(72136852453/41075000000000 : ℝ)*(4041/25000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (16424961856241677791/16430000000000000000 : ℝ)+2*(72136852453/41075000000000 : ℝ)*(4041/25000 : ℝ)=(10002611087587389/10000000000000000 : ℝ) by norm_num, show 1+2*(53924473743693417/100000000000000000000 : ℝ)=(50053924473743693417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16424961856241677791/16430000000000000000 : ℝ)*(X 1 0+X 2 0)+(72136852453/41075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (1199/12500 : ℝ)) (hi := (4041/25000 : ℝ)) (c := (16424961856241677791/16430000000000000000 : ℝ)) (alpha := (72136852453/41075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16424961856241677791/16430000000000000000 : ℝ)*(X 0 1+X 2 1)+(72136852453/41075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (1199/12500 : ℝ)) (hi := (4041/25000 : ℝ)) (c := (16424961856241677791/16430000000000000000 : ℝ)) (alpha := (72136852453/41075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16424961856241677791/16430000000000000000 : ℝ)*(X 0 2+X 1 2)+(72136852453/41075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (1199/12500 : ℝ)) (hi := (4041/25000 : ℝ)) (c := (16424961856241677791/16430000000000000000 : ℝ)) (alpha := (72136852453/41075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1053377881/5000000000 : ℝ)*X 0 0+(5417678761/10000000000 : ℝ)*X 0 1+(5242350311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350987731/10000000000 : ℝ)*X 1 0+(-68630023/312500000 : ℝ)*X 1 1+(209694017/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337746929/2500000000 : ℝ)*X 2 0+(327646931/625000000 : ℝ)*X 2 1+(-2196160133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173018891/5000000000 : ℝ)*X 0 0+(2085481077/5000000000 : ℝ)*X 0 1+(905641331/2000000000 : ℝ)*X 0 2+(2173018891/5000000000 : ℝ)*X 1 0+(2085481077/5000000000 : ℝ)*X 1 1+(905641331/2000000000 : ℝ)*X 1 2+(2173018891/5000000000 : ℝ)*X 2 0+(2085481077/5000000000 : ℝ)*X 2 1+(905641331/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2106769671/10000000000 : ℝ)*X 0 0+(262148929/500000000 : ℝ)*X 0 1+(5417046753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2653094781/5000000000 : ℝ)*X 1 0+(-20214637/100000000 : ℝ)*X 1 1+(541704659/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653094443/5000000000 : ℝ)*X 2 0+(2708523517/5000000000 : ℝ)*X 2 1+(-505366003/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173032729/5000000000 : ℝ)*X 0 0+(1131731431/2500000000 : ℝ)*X 0 1+(4172248997/10000000000 : ℝ)*X 0 2+(2173032729/5000000000 : ℝ)*X 1 0+(1131731431/2500000000 : ℝ)*X 1 1+(4172248997/10000000000 : ℝ)*X 1 2+(2173032729/5000000000 : ℝ)*X 2 0+(1131731431/2500000000 : ℝ)*X 2 1+(4172248997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-90745997/10000000000 : ℝ)*X 0 0+(2952329841/5000000000 : ℝ)*X 0 1+(1180933529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((979873279/10000000000 : ℝ)*X 1 0+(-87462423/200000000 : ℝ)*X 1 1+(3470178461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((24496609/250000000 : ℝ)*X 2 0+(6940336849/10000000000 : ℝ)*X 2 1+(-874629989/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (409358980611143305626296691/41075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3852679/50000000000000 : ℝ)*(lower2) + (417710299/100000000000000 : ℝ)*(lower4) + (212570870274033/5000000000000 : ℝ)*(major0) + (212570870274033/5000000000000 : ℝ)*(major1) + (212570870274033/5000000000000 : ℝ)*(major2) + (712950932011777/12500000000000 : ℝ)*(sp0) + (5703609107155789/100000000000000 : ℝ)*(sp1) + (570362297343577/10000000000000 : ℝ)*(sp2) + (1399604492343453/50000000000000 : ℝ)*(sp3) + (7923464569/50000000000000 : ℝ)*(sp4) + (14937784921/100000000000000 : ℝ)*(sp5) + (144912919/10000000000000 : ℝ)*(sp7) + (185479339/25000000000000 : ℝ)*(sp8) + (1071504941/100000000000000 : ℝ)*(sp10) + (87475326056753/3125000000000 : ℝ)*(f.failure) + (570362404494071/10000000000000 : ℝ)*(f.sum) + (8928471613293/821500000000000000000000000 : ℝ)*base66 + (1429681847551901103/82150000000000000000000000000000 : ℝ)*base67 + (1402750754514201103/82150000000000000000000000000000 : ℝ)*base69 + (4876487960322751103/82150000000000000000000000000000 : ℝ)*base71 + (144263185007/205375000000000000000000000 : ℝ)*base74 + (84804440846548897/82150000000000000000000000000000 : ℝ)*base76 + (11091745634343098897/82150000000000000000000000000000 : ℝ)*base78 + (93383153186751103/82150000000000000000000000000000 : ℝ)*base79 + (488770432369/1643000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (76377/78125000000000000000 : ℝ)*base90 + (76377/78125000000000000000 : ℝ)*base92 + (76377/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2098024066557491806477205277/821500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546218479/100000000000000 : ℝ)*(lower4) + (4282174600503317/100000000000000 : ℝ)*(major0) + (4282174600503317/100000000000000 : ℝ)*(major1) + (4282174600503317/100000000000000 : ℝ)*(major2) + (3423081299/25000000000000 : ℝ)*(sp0) + (2817188731/50000000000000 : ℝ)*(sp1) + (5444692299/100000000000000 : ℝ)*(sp2) + (5744871372509941/100000000000000 : ℝ)*(sp4) + (2872440727064477/50000000000000 : ℝ)*(sp5) + (5744881280886483/100000000000000 : ℝ)*(sp6) + (176216345601861/6250000000000 : ℝ)*(sp7) + (630352977/25000000000000 : ℝ)*(sp8) + (497740629/100000000000000 : ℝ)*(sp9) + (860668263/100000000000000 : ℝ)*(sp10) + (176216345601861/6250000000000 : ℝ)*(f.failure) + (1148977517249409/20000000000000 : ℝ)*(f.sum) + (25228092625069/8215000000000000000000000000 : ℝ)*base65 + (552843998493132747/1643000000000000000000000000000000 : ℝ)*base67 + (8882883827158132747/1643000000000000000000000000000000 : ℝ)*base69 + (11879932854314132747/1643000000000000000000000000000000 : ℝ)*base71 + (572144946187/4107500000000000000000000000 : ℝ)*base73 + (5186876530521132747/1643000000000000000000000000000000 : ℝ)*base75 + (2619353382051132747/1643000000000000000000000000000000 : ℝ)*base77 + (5909360121790132747/1643000000000000000000000000000000 : ℝ)*base79 + (2465205717997/4107500000000000000000000000 : ℝ)*base81 + (1431449/156250000000000000000 : ℝ)*base90 + (1431449/156250000000000000000 : ℝ)*base92 + (1431449/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1265_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1265_s4_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108912201/10000000000 : ℝ)*x 0 + (215863187/400000000 : ℝ)*x 1 + (5262035449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108912201/10000000000 : ℝ)^4229 ≤ (6413050606911/50000000000000 : ℝ)^3205 := by
    have hnat : (2108912201 : ℕ)^4229*50000000000000^3205 ≤ 6413050606911^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108912201 10000000000 6413050606911 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215863187/400000000 : ℝ)^4229 ≤ (44312910426249/100000000000000 : ℝ)^3205 := by
    have hnat : (215863187 : ℕ)^4229*100000000000000^3205 ≤ 44312910426249^3205*400000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215863187 400000000 44312910426249 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262035449/10000000000 : ℝ)^4229 ≤ (21430494171563/50000000000000 : ℝ)^3205 := by
    have hnat : (5262035449 : ℕ)^4229*50000000000000^3205 ≤ 21430494171563^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262035449 10000000000 21430494171563 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108912201/10000000000 : ℝ), (215863187/400000000 : ℝ), (5262035449/10000000000 : ℝ)] ![(6413050606911/50000000000000 : ℝ), (44312910426249/100000000000000 : ℝ), (21430494171563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108912201/10000000000 : ℝ)|^4229 ≤ (6413050606911/50000000000000 : ℝ)^3205
        have hw : |(-2108912201/10000000000 : ℝ)|=(2108912201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215863187/400000000 : ℝ)|^4229 ≤ (44312910426249/100000000000000 : ℝ)^3205
        have hw : |(215863187/400000000 : ℝ)|=(215863187/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262035449/10000000000 : ℝ)|^4229 ≤ (21430494171563/50000000000000 : ℝ)^3205
        have hw : |(5262035449/10000000000 : ℝ)|=(5262035449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069131393/2000000000 : ℝ)*x 0 + (-2177209883/10000000000 : ℝ)*x 1 + (5262035407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069131393/2000000000 : ℝ)^4229 ≤ (2188100299297/5000000000000 : ℝ)^3205 := by
    have hnat : (1069131393 : ℕ)^4229*5000000000000^3205 ≤ 2188100299297^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069131393 2000000000 2188100299297 5000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177209883/10000000000 : ℝ)^4229 ≤ (6688503055797/50000000000000 : ℝ)^3205 := by
    have hnat : (2177209883 : ℕ)^4229*50000000000000^3205 ≤ 6688503055797^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177209883 10000000000 6688503055797 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262035407/10000000000 : ℝ)^4229 ≤ (1071524697293/2500000000000 : ℝ)^3205 := by
    have hnat : (5262035407 : ℕ)^4229*2500000000000^3205 ≤ 1071524697293^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262035407 10000000000 1071524697293 2500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069131393/2000000000 : ℝ), (-2177209883/10000000000 : ℝ), (5262035407/10000000000 : ℝ)] ![(2188100299297/5000000000000 : ℝ), (6688503055797/50000000000000 : ℝ), (1071524697293/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069131393/2000000000 : ℝ)|^4229 ≤ (2188100299297/5000000000000 : ℝ)^3205
        have hw : |(1069131393/2000000000 : ℝ)|=(1069131393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177209883/10000000000 : ℝ)|^4229 ≤ (6688503055797/50000000000000 : ℝ)^3205
        have hw : |(-2177209883/10000000000 : ℝ)|=(2177209883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262035407/10000000000 : ℝ)|^4229 ≤ (1071524697293/2500000000000 : ℝ)^3205
        have hw : |(5262035407/10000000000 : ℝ)|=(5262035407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069131409/2000000000 : ℝ)*x 0 + (2631017663/5000000000 : ℝ)*x 1 + (-2177209883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069131409/2000000000 : ℝ)^4229 ≤ (5470250856263/12500000000000 : ℝ)^3205 := by
    have hnat : (1069131409 : ℕ)^4229*12500000000000^3205 ≤ 5470250856263^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069131409 2000000000 5470250856263 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631017663/5000000000 : ℝ)^4229 ≤ (42860987021151/100000000000000 : ℝ)^3205 := by
    have hnat : (2631017663 : ℕ)^4229*100000000000000^3205 ≤ 42860987021151^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631017663 5000000000 42860987021151 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177209883/10000000000 : ℝ)^4229 ≤ (6688503055797/50000000000000 : ℝ)^3205 := by
    have hnat : (2177209883 : ℕ)^4229*50000000000000^3205 ≤ 6688503055797^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177209883 10000000000 6688503055797 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069131409/2000000000 : ℝ), (2631017663/5000000000 : ℝ), (-2177209883/10000000000 : ℝ)] ![(5470250856263/12500000000000 : ℝ), (42860987021151/100000000000000 : ℝ), (6688503055797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069131409/2000000000 : ℝ)|^4229 ≤ (5470250856263/12500000000000 : ℝ)^3205
        have hw : |(1069131409/2000000000 : ℝ)|=(1069131409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631017663/5000000000 : ℝ)|^4229 ≤ (42860987021151/100000000000000 : ℝ)^3205
        have hw : |(2631017663/5000000000 : ℝ)|=(2631017663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177209883/10000000000 : ℝ)|^4229 ≤ (6688503055797/50000000000000 : ℝ)^3205
        have hw : |(-2177209883/10000000000 : ℝ)|=(2177209883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347330373/10000000000 : ℝ)*x 0 + (421234749/1000000000 : ℝ)*x 1 + (4486492727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347330373/10000000000 : ℝ)^4229 ≤ (16657295982683/50000000000000 : ℝ)^3205 := by
    have hnat : (4347330373 : ℕ)^4229*50000000000000^3205 ≤ 16657295982683^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347330373 10000000000 16657295982683 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421234749/1000000000 : ℝ)^4229 ≤ (15978256204113/50000000000000 : ℝ)^3205 := by
    have hnat : (421234749 : ℕ)^4229*50000000000000^3205 ≤ 15978256204113^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421234749 1000000000 15978256204113 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486492727/10000000000 : ℝ)^4229 ≤ (17364447805091/50000000000000 : ℝ)^3205 := by
    have hnat : (4486492727 : ℕ)^4229*50000000000000^3205 ≤ 17364447805091^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486492727 10000000000 17364447805091 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347330373/10000000000 : ℝ), (421234749/1000000000 : ℝ), (4486492727/10000000000 : ℝ)] ![(16657295982683/50000000000000 : ℝ), (15978256204113/50000000000000 : ℝ), (17364447805091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347330373/10000000000 : ℝ)|^4229 ≤ (16657295982683/50000000000000 : ℝ)^3205
        have hw : |(4347330373/10000000000 : ℝ)|=(4347330373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(421234749/1000000000 : ℝ)|^4229 ≤ (15978256204113/50000000000000 : ℝ)^3205
        have hw : |(421234749/1000000000 : ℝ)|=(421234749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486492727/10000000000 : ℝ)|^4229 ≤ (17364447805091/50000000000000 : ℝ)^3205
        have hw : |(4486492727/10000000000 : ℝ)|=(4486492727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108918379/10000000000 : ℝ)*x 0 + (1052481203/2000000000 : ℝ)*x 1 + (2698103751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108918379/10000000000 : ℝ)^4229 ≤ (12826150792383/100000000000000 : ℝ)^3205 := by
    have hnat : (2108918379 : ℕ)^4229*100000000000000^3205 ≤ 12826150792383^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108918379 10000000000 12826150792383 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052481203/2000000000 : ℝ)^4229 ≤ (4286497114331/10000000000000 : ℝ)^3205 := by
    have hnat : (1052481203 : ℕ)^4229*10000000000000^3205 ≤ 4286497114331^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052481203 2000000000 4286497114331 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698103751/5000000000 : ℝ)^4229 ≤ (44308878046627/100000000000000 : ℝ)^3205 := by
    have hnat : (2698103751 : ℕ)^4229*100000000000000^3205 ≤ 44308878046627^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698103751 5000000000 44308878046627 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108918379/10000000000 : ℝ), (1052481203/2000000000 : ℝ), (2698103751/5000000000 : ℝ)] ![(12826150792383/100000000000000 : ℝ), (4286497114331/10000000000000 : ℝ), (44308878046627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108918379/10000000000 : ℝ)|^4229 ≤ (12826150792383/100000000000000 : ℝ)^3205
        have hw : |(-2108918379/10000000000 : ℝ)|=(2108918379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052481203/2000000000 : ℝ)|^4229 ≤ (4286497114331/10000000000000 : ℝ)^3205
        have hw : |(1052481203/2000000000 : ℝ)|=(1052481203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698103751/5000000000 : ℝ)|^4229 ≤ (44308878046627/100000000000000 : ℝ)^3205
        have hw : |(2698103751/5000000000 : ℝ)|=(2698103751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655638069/5000000000 : ℝ)*x 0 + (-127689859/625000000 : ℝ)*x 1 + (5396207711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655638069/5000000000 : ℝ)^4229 ≤ (21695502522873/50000000000000 : ℝ)^3205 := by
    have hnat : (2655638069 : ℕ)^4229*50000000000000^3205 ≤ 21695502522873^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655638069 5000000000 21695502522873 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127689859/625000000 : ℝ)^4229 ≤ (2460022925111/20000000000000 : ℝ)^3205 := by
    have hnat : (127689859 : ℕ)^4229*20000000000000^3205 ≤ 2460022925111^3205*625000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127689859 625000000 2460022925111 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396207711/10000000000 : ℝ)^4229 ≤ (11077220077763/25000000000000 : ℝ)^3205 := by
    have hnat : (5396207711 : ℕ)^4229*25000000000000^3205 ≤ 11077220077763^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396207711 10000000000 11077220077763 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655638069/5000000000 : ℝ), (-127689859/625000000 : ℝ), (5396207711/10000000000 : ℝ)] ![(21695502522873/50000000000000 : ℝ), (2460022925111/20000000000000 : ℝ), (11077220077763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655638069/5000000000 : ℝ)|^4229 ≤ (21695502522873/50000000000000 : ℝ)^3205
        have hw : |(2655638069/5000000000 : ℝ)|=(2655638069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127689859/625000000 : ℝ)|^4229 ≤ (2460022925111/20000000000000 : ℝ)^3205
        have hw : |(-127689859/625000000 : ℝ)|=(127689859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396207711/10000000000 : ℝ)|^4229 ≤ (11077220077763/25000000000000 : ℝ)^3205
        have hw : |(5396207711/10000000000 : ℝ)|=(5396207711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311276143/10000000000 : ℝ)*x 0 + (5396207947/10000000000 : ℝ)*x 1 + (-255379677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311276143/10000000000 : ℝ)^4229 ≤ (8678201019929/20000000000000 : ℝ)^3205 := by
    have hnat : (5311276143 : ℕ)^4229*20000000000000^3205 ≤ 8678201019929^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311276143 10000000000 8678201019929 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396207947/10000000000 : ℝ)^4229 ≤ (11077220717003/25000000000000 : ℝ)^3205 := by
    have hnat : (5396207947 : ℕ)^4229*25000000000000^3205 ≤ 11077220717003^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396207947 10000000000 11077220717003 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255379677/1250000000 : ℝ)^4229 ≤ (192189250311/1562500000000 : ℝ)^3205 := by
    have hnat : (255379677 : ℕ)^4229*1562500000000^3205 ≤ 192189250311^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255379677 1250000000 192189250311 1562500000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311276143/10000000000 : ℝ), (5396207947/10000000000 : ℝ), (-255379677/1250000000 : ℝ)] ![(8678201019929/20000000000000 : ℝ), (11077220717003/25000000000000 : ℝ), (192189250311/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311276143/10000000000 : ℝ)|^4229 ≤ (8678201019929/20000000000000 : ℝ)^3205
        have hw : |(5311276143/10000000000 : ℝ)|=(5311276143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396207947/10000000000 : ℝ)|^4229 ≤ (11077220717003/25000000000000 : ℝ)^3205
        have hw : |(5396207947/10000000000 : ℝ)|=(5396207947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255379677/1250000000 : ℝ)|^4229 ≤ (192189250311/1562500000000 : ℝ)^3205
        have hw : |(-255379677/1250000000 : ℝ)|=(255379677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s4_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347342687/10000000000 : ℝ)*x 0 + (2242868931/5000000000 : ℝ)*x 1 + (2106552617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347342687/10000000000 : ℝ)^4229 ≤ (3331471648013/10000000000000 : ℝ)^3205 := by
    have hnat : (4347342687 : ℕ)^4229*10000000000000^3205 ≤ 3331471648013^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347342687 10000000000 3331471648013 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242868931/5000000000 : ℝ)^4229 ≤ (34721185665329/100000000000000 : ℝ)^3205 := by
    have hnat : (2242868931 : ℕ)^4229*100000000000000^3205 ≤ 34721185665329^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242868931 5000000000 34721185665329 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106552617/5000000000 : ℝ)^4229 ≤ (6392819566311/20000000000000 : ℝ)^3205 := by
    have hnat : (2106552617 : ℕ)^4229*20000000000000^3205 ≤ 6392819566311^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106552617 5000000000 6392819566311 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347342687/10000000000 : ℝ), (2242868931/5000000000 : ℝ), (2106552617/5000000000 : ℝ)] ![(3331471648013/10000000000000 : ℝ), (34721185665329/100000000000000 : ℝ), (6392819566311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347342687/10000000000 : ℝ)|^4229 ≤ (3331471648013/10000000000000 : ℝ)^3205
        have hw : |(4347342687/10000000000 : ℝ)|=(4347342687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242868931/5000000000 : ℝ)|^4229 ≤ (34721185665329/100000000000000 : ℝ)^3205
        have hw : |(2242868931/5000000000 : ℝ)|=(2242868931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106552617/5000000000 : ℝ)|^4229 ≤ (6392819566311/20000000000000 : ℝ)^3205
        have hw : |(2106552617/5000000000 : ℝ)|=(2106552617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10969/100000 : ℝ) ^ (8457/2048 : ℝ) ≤ (10876045343381399/100000000000000000000 : ℝ) := by
    have hpowers : (10969/100000 : ℝ)^8457 ≤ (10876045343381399/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10969 : ℕ)^8457*100000000000000000000^2048 ≤ 10876045343381399^2048*100000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10969 100000 10876045343381399 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10969/100000 : ℝ)) (X := (10876045343381399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (367/2500 : ℝ) ^ (8457/2048 : ℝ) ≤ (36231234413135099/100000000000000000000 : ℝ) := by
    have hpowers : (367/2500 : ℝ)^8457 ≤ (36231234413135099/100000000000000000000 : ℝ)^2048 := by
      have hnat : (367 : ℕ)^8457*100000000000000000000^2048 ≤ 36231234413135099^2048*2500^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        367 2500 36231234413135099 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (367/2500 : ℝ)) (X := (36231234413135099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010876045343381399/50000000000000000000 : ℝ) ≤ (10000526718817793/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50010876045343381399/50000000000000000000 : ℝ)^2048 ≤ (10000526718817793/10000000000000000 : ℝ)^8457 := by
      have hnat : (50010876045343381399 : ℕ)^2048*10000000000000000^8457 ≤ 10000526718817793^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010876045343381399 50000000000000000000 10000526718817793 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000526718817793/10000000000000000 : ℝ)) (X := (50010876045343381399/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023553639878258249/50000000000000000000 : ℝ) ≤ (2500285143942967/2500000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50023553639878258249/50000000000000000000 : ℝ)^2048 ≤ (2500285143942967/2500000000000000 : ℝ)^8457 := by
      have hnat : (50023553639878258249 : ℕ)^2048*2500000000000000^8457 ≤ 2500285143942967^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023553639878258249 50000000000000000000 2500285143942967 2500000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500285143942967/2500000000000000 : ℝ)) (X := (50023553639878258249/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036231234413135099/50000000000000000000 : ℝ) ≤ (10001754432725943/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50036231234413135099/50000000000000000000 : ℝ)^2048 ≤ (10001754432725943/10000000000000000 : ℝ)^8457 := by
      have hnat : (50036231234413135099 : ℕ)^2048*10000000000000000^8457 ≤ 10001754432725943^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036231234413135099 50000000000000000000 10001754432725943 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001754432725943/10000000000000000 : ℝ)) (X := (50036231234413135099/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10876045343381399/100000000000000000000 : ℝ) ≤ ((37098487859674332473/37110000000000000000 : ℝ)+2*(24554278163/14844000000000 : ℝ)*(10969/100000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (37098487859674332473/37110000000000000000 : ℝ)+2*(24554278163/14844000000000 : ℝ)*(10969/100000 : ℝ)=(10000526718817793/10000000000000000 : ℝ) by norm_num, show 1+2*(10876045343381399/100000000000000000000 : ℝ)=(50010876045343381399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36231234413135099/100000000000000000000 : ℝ)+(10876045343381399/100000000000000000000 : ℝ) ≤ ((37098487859674332473/37110000000000000000 : ℝ)+(24554278163/14844000000000 : ℝ)*((367/2500 : ℝ)+(10969/100000 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (37098487859674332473/37110000000000000000 : ℝ)+(24554278163/14844000000000 : ℝ)*((367/2500 : ℝ)+(10969/100000 : ℝ))=(2500285143942967/2500000000000000 : ℝ) by norm_num, show 1+(36231234413135099/100000000000000000000 : ℝ)+(10876045343381399/100000000000000000000 : ℝ)=(50023553639878258249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36231234413135099/100000000000000000000 : ℝ) ≤ ((37098487859674332473/37110000000000000000 : ℝ)+2*(24554278163/14844000000000 : ℝ)*(367/2500 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (37098487859674332473/37110000000000000000 : ℝ)+2*(24554278163/14844000000000 : ℝ)*(367/2500 : ℝ)=(10001754432725943/10000000000000000 : ℝ) by norm_num, show 1+2*(36231234413135099/100000000000000000000 : ℝ)=(50036231234413135099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37098487859674332473/37110000000000000000 : ℝ)*(X 1 0+X 2 0)+(24554278163/14844000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (37098487859674332473/37110000000000000000 : ℝ)) (alpha := (24554278163/14844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37098487859674332473/37110000000000000000 : ℝ)*(X 0 1+X 2 1)+(24554278163/14844000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (37098487859674332473/37110000000000000000 : ℝ)) (alpha := (24554278163/14844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37098487859674332473/37110000000000000000 : ℝ)*(X 0 2+X 1 2)+(24554278163/14844000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (37098487859674332473/37110000000000000000 : ℝ)) (alpha := (24554278163/14844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108912201/10000000000 : ℝ)*X 0 0+(215863187/400000000 : ℝ)*X 0 1+(5262035449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069131393/2000000000 : ℝ)*X 1 0+(-2177209883/10000000000 : ℝ)*X 1 1+(5262035407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069131409/2000000000 : ℝ)*X 2 0+(2631017663/5000000000 : ℝ)*X 2 1+(-2177209883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347330373/10000000000 : ℝ)*X 0 0+(421234749/1000000000 : ℝ)*X 0 1+(4486492727/10000000000 : ℝ)*X 0 2+(4347330373/10000000000 : ℝ)*X 1 0+(421234749/1000000000 : ℝ)*X 1 1+(4486492727/10000000000 : ℝ)*X 1 2+(4347330373/10000000000 : ℝ)*X 2 0+(421234749/1000000000 : ℝ)*X 2 1+(4486492727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108918379/10000000000 : ℝ)*X 0 0+(1052481203/2000000000 : ℝ)*X 0 1+(2698103751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655638069/5000000000 : ℝ)*X 1 0+(-127689859/625000000 : ℝ)*X 1 1+(5396207711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311276143/10000000000 : ℝ)*X 2 0+(5396207947/10000000000 : ℝ)*X 2 1+(-255379677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347342687/10000000000 : ℝ)*X 0 0+(2242868931/5000000000 : ℝ)*X 0 1+(2106552617/5000000000 : ℝ)*X 0 2+(4347342687/10000000000 : ℝ)*X 1 0+(2242868931/5000000000 : ℝ)*X 1 1+(2106552617/5000000000 : ℝ)*X 1 2+(4347342687/10000000000 : ℝ)*X 2 0+(2242868931/5000000000 : ℝ)*X 2 1+(2106552617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1668172491738314150897720307/309250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103834097/12500000000000 : ℝ)*(base19) + (436410719/50000000000000 : ℝ)*(base23) + (102163479/100000000000000 : ℝ)*(upper3) + (36929069/100000000000000 : ℝ)*(upper4) + (14423359/20000000000000 : ℝ)*(upper5) + (5540130455337141/100000000000000 : ℝ)*(major0) + (5540130455337141/100000000000000 : ℝ)*(major1) + (5540130455337141/100000000000000 : ℝ)*(major2) + (7432518827235857/100000000000000 : ℝ)*(sp0) + (297301495552171/4000000000000 : ℝ)*(sp1) + (7432537346655613/100000000000000 : ℝ)*(sp2) + (455963909187639/12500000000000 : ℝ)*(sp3) + (19392241193/100000000000000 : ℝ)*(sp4) + (2247577541/20000000000000 : ℝ)*(sp7) + (1823861255694409/50000000000000 : ℝ)*(f.failure) + (7432538219477051/100000000000000 : ℝ)*(f.sum) + (2975203879373/618500000000000000000000000 : ℝ)*base65 + (11486602433245593231/1237000000000000000000000000000000 : ℝ)*base67 + (3331671134464593231/1237000000000000000000000000000000 : ℝ)*base69 + (13720889737583593231/1237000000000000000000000000000000 : ℝ)*base71 + (49522571/618500000000000000000000 : ℝ)*base73 + (5848916350162593231/1237000000000000000000000000000000 : ℝ)*base75 + (2406399311813593231/1237000000000000000000000000000000 : ℝ)*base77 + (4434580219670406769/1237000000000000000000000000000000 : ℝ)*base80 + (15647492841/24740000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7098519/1250000000000000000000 : ℝ)*base89 + (7098519/1250000000000000000000 : ℝ)*base91 + (7098519/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11893640024794594314047/1237000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34897967/2500000000000 : ℝ)*(base19) + (183596507/10000000000000 : ℝ)*(base23) + (54123469/50000000000000 : ℝ)*(upper2) + (206846603/50000000000000 : ℝ)*(upper3) + (59140817/50000000000000 : ℝ)*(upper5) + (2785422293192239/50000000000000 : ℝ)*(major0) + (2785422293192239/50000000000000 : ℝ)*(major1) + (2785422293192239/50000000000000 : ℝ)*(major2) + (14353185761/50000000000000 : ℝ)*(sp1) + (64114623173/100000000000000 : ℝ)*(sp2) + (3736871799586511/50000000000000 : ℝ)*(sp4) + (373685674844141/5000000000000 : ℝ)*(sp5) + (373683882429239/5000000000000 : ℝ)*(sp6) + (3667945253099021/100000000000000 : ℝ)*(sp7) + (3667945253099021/100000000000000 : ℝ)*(f.failure) + (3736871799586511/50000000000000 : ℝ)*(f.sum) + (203888021291/3711000000000000000000000000 : ℝ)*base65 + (19709253384594222953/1855500000000000000000000000000000 : ℝ)*base68 + (10434408196412777047/1855500000000000000000000000000000 : ℝ)*base69 + (17473281040711722953/1855500000000000000000000000000000 : ℝ)*base72 + (5885912219843/1855500000000000000000000000 : ℝ)*base74 + (9143920137047777047/1855500000000000000000000000000000 : ℝ)*base75 + (7966537913645777047/1855500000000000000000000000000000 : ℝ)*base77 + (43171918639398222953/1855500000000000000000000000000000 : ℝ)*base80 + (179203488671/742200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (20325389/2500000000000000000000 : ℝ)*base90 + (20325389/2500000000000000000000 : ℝ)*base92 + (20325389/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1265_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1265_s5_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-527330929/2500000000 : ℝ)*x 0 + (336991377/625000000 : ℝ)*x 1 + (5266482761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527330929/2500000000 : ℝ)^4229 ≤ (6414701865259/50000000000000 : ℝ)^3205 := by
    have hnat : (527330929 : ℕ)^4229*50000000000000^3205 ≤ 6414701865259^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527330929 2500000000 6414701865259 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336991377/625000000 : ℝ)^4229 ≤ (44261802796527/100000000000000 : ℝ)^3205 := by
    have hnat : (336991377 : ℕ)^4229*100000000000000^3205 ≤ 44261802796527^3205*625000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336991377 625000000 44261802796527 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266482761/10000000000 : ℝ)^4229 ≤ (8581758689771/20000000000000 : ℝ)^3205 := by
    have hnat : (5266482761 : ℕ)^4229*20000000000000^3205 ≤ 8581758689771^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266482761 10000000000 8581758689771 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527330929/2500000000 : ℝ), (336991377/625000000 : ℝ), (5266482761/10000000000 : ℝ)] ![(6414701865259/50000000000000 : ℝ), (44261802796527/100000000000000 : ℝ), (8581758689771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527330929/2500000000 : ℝ)|^4229 ≤ (6414701865259/50000000000000 : ℝ)^3205
        have hw : |(-527330929/2500000000 : ℝ)|=(527330929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336991377/625000000 : ℝ)|^4229 ≤ (44261802796527/100000000000000 : ℝ)^3205
        have hw : |(336991377/625000000 : ℝ)|=(336991377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266482761/10000000000 : ℝ)|^4229 ≤ (8581758689771/20000000000000 : ℝ)^3205
        have hw : |(5266482761/10000000000 : ℝ)|=(5266482761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068892367/2000000000 : ℝ)*x 0 + (-543226037/2500000000 : ℝ)*x 1 + (1316620691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068892367/2000000000 : ℝ)^4229 ≤ (43749096604829/100000000000000 : ℝ)^3205 := by
    have hnat : (1068892367 : ℕ)^4229*100000000000000^3205 ≤ 43749096604829^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068892367 2000000000 43749096604829 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543226037/2500000000 : ℝ)^4229 ≤ (1334210989951/10000000000000 : ℝ)^3205 := by
    have hnat : (543226037 : ℕ)^4229*10000000000000^3205 ≤ 1334210989951^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543226037 2500000000 1334210989951 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316620691/2500000000 : ℝ)^4229 ≤ (42908793481107/100000000000000 : ℝ)^3205 := by
    have hnat : (1316620691 : ℕ)^4229*100000000000000^3205 ≤ 42908793481107^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316620691 2500000000 42908793481107 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068892367/2000000000 : ℝ), (-543226037/2500000000 : ℝ), (1316620691/2500000000 : ℝ)] ![(43749096604829/100000000000000 : ℝ), (1334210989951/10000000000000 : ℝ), (42908793481107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068892367/2000000000 : ℝ)|^4229 ≤ (43749096604829/100000000000000 : ℝ)^3205
        have hw : |(1068892367/2000000000 : ℝ)|=(1068892367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543226037/2500000000 : ℝ)|^4229 ≤ (1334210989951/10000000000000 : ℝ)^3205
        have hw : |(-543226037/2500000000 : ℝ)|=(543226037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316620691/2500000000 : ℝ)|^4229 ≤ (42908793481107/100000000000000 : ℝ)^3205
        have hw : |(1316620691/2500000000 : ℝ)|=(1316620691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068892381/2000000000 : ℝ)*x 0 + (1053296537/2000000000 : ℝ)*x 1 + (-2172904159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068892381/2000000000 : ℝ)^4229 ≤ (21874548680459/50000000000000 : ℝ)^3205 := by
    have hnat : (1068892381 : ℕ)^4229*50000000000000^3205 ≤ 21874548680459^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068892381 2000000000 21874548680459 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053296537/2000000000 : ℝ)^4229 ≤ (8581758526361/20000000000000 : ℝ)^3205 := by
    have hnat : (1053296537 : ℕ)^4229*20000000000000^3205 ≤ 8581758526361^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053296537 2000000000 8581758526361 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172904159/10000000000 : ℝ)^4229 ≤ (13342109988633/100000000000000 : ℝ)^3205 := by
    have hnat : (2172904159 : ℕ)^4229*100000000000000^3205 ≤ 13342109988633^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172904159 10000000000 13342109988633 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068892381/2000000000 : ℝ), (1053296537/2000000000 : ℝ), (-2172904159/10000000000 : ℝ)] ![(21874548680459/50000000000000 : ℝ), (8581758526361/20000000000000 : ℝ), (13342109988633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068892381/2000000000 : ℝ)|^4229 ≤ (21874548680459/50000000000000 : ℝ)^3205
        have hw : |(1068892381/2000000000 : ℝ)|=(1068892381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053296537/2000000000 : ℝ)|^4229 ≤ (8581758526361/20000000000000 : ℝ)^3205
        have hw : |(1053296537/2000000000 : ℝ)|=(1053296537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172904159/10000000000 : ℝ)|^4229 ≤ (13342109988633/100000000000000 : ℝ)^3205
        have hw : |(-2172904159/10000000000 : ℝ)|=(2172904159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347574437/10000000000 : ℝ)*x 0 + (2110826791/5000000000 : ℝ)*x 1 + (895424853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347574437/10000000000 : ℝ)^4229 ≤ (6663411974853/20000000000000 : ℝ)^3205 := by
    have hnat : (4347574437 : ℕ)^4229*20000000000000^3205 ≤ 6663411974853^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347574437 10000000000 6663411974853 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110826791/5000000000 : ℝ)^4229 ≤ (4006212694751/12500000000000 : ℝ)^3205 := by
    have hnat : (2110826791 : ℕ)^4229*12500000000000^3205 ≤ 4006212694751^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110826791 5000000000 4006212694751 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895424853/2000000000 : ℝ)^4229 ≤ (34633238558789/100000000000000 : ℝ)^3205 := by
    have hnat : (895424853 : ℕ)^4229*100000000000000^3205 ≤ 34633238558789^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895424853 2000000000 34633238558789 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347574437/10000000000 : ℝ), (2110826791/5000000000 : ℝ), (895424853/2000000000 : ℝ)] ![(6663411974853/20000000000000 : ℝ), (4006212694751/12500000000000 : ℝ), (34633238558789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347574437/10000000000 : ℝ)|^4229 ≤ (6663411974853/20000000000000 : ℝ)^3205
        have hw : |(4347574437/10000000000 : ℝ)|=(4347574437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110826791/5000000000 : ℝ)|^4229 ≤ (4006212694751/12500000000000 : ℝ)^3205
        have hw : |(2110826791/5000000000 : ℝ)|=(2110826791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895424853/2000000000 : ℝ)|^4229 ≤ (34633238558789/100000000000000 : ℝ)^3205
        have hw : |(895424853/2000000000 : ℝ)|=(895424853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109328653/10000000000 : ℝ)*x 0 + (526680461/1000000000 : ℝ)*x 1 + (539153893/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109328653/10000000000 : ℝ)^4229 ≤ (6414721676249/50000000000000 : ℝ)^3205 := by
    have hnat : (2109328653 : ℕ)^4229*50000000000000^3205 ≤ 6414721676249^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109328653 10000000000 6414721676249 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526680461/1000000000 : ℝ)^4229 ≤ (1072806339327/2500000000000 : ℝ)^3205 := by
    have hnat : (526680461 : ℕ)^4229*2500000000000^3205 ≤ 1072806339327^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526680461 1000000000 1072806339327 2500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539153893/1000000000 : ℝ)^4229 ≤ (44258303059051/100000000000000 : ℝ)^3205 := by
    have hnat : (539153893 : ℕ)^4229*100000000000000^3205 ≤ 44258303059051^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539153893 1000000000 44258303059051 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109328653/10000000000 : ℝ), (526680461/1000000000 : ℝ), (539153893/1000000000 : ℝ)] ![(6414721676249/50000000000000 : ℝ), (1072806339327/2500000000000 : ℝ), (44258303059051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109328653/10000000000 : ℝ)|^4229 ≤ (6414721676249/50000000000000 : ℝ)^3205
        have hw : |(-2109328653/10000000000 : ℝ)|=(2109328653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526680461/1000000000 : ℝ)|^4229 ≤ (1072806339327/2500000000000 : ℝ)^3205
        have hw : |(526680461/1000000000 : ℝ)|=(526680461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539153893/1000000000 : ℝ)|^4229 ≤ (44258303059051/100000000000000 : ℝ)^3205
        have hw : |(539153893/1000000000 : ℝ)|=(539153893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328105463/2500000000 : ℝ)*x 0 + (-2047847843/10000000000 : ℝ)*x 1 + (1347884737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328105463/2500000000 : ℝ)^4229 ≤ (43403356032741/100000000000000 : ℝ)^3205 := by
    have hnat : (1328105463 : ℕ)^4229*100000000000000^3205 ≤ 43403356032741^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328105463 2500000000 43403356032741 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047847843/10000000000 : ℝ)^4229 ≤ (6169170348243/50000000000000 : ℝ)^3205 := by
    have hnat : (2047847843 : ℕ)^4229*50000000000000^3205 ≤ 6169170348243^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047847843 10000000000 6169170348243 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347884737/2500000000 : ℝ)^4229 ≤ (44258303254019/100000000000000 : ℝ)^3205 := by
    have hnat : (1347884737 : ℕ)^4229*100000000000000^3205 ≤ 44258303254019^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347884737 2500000000 44258303254019 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328105463/2500000000 : ℝ), (-2047847843/10000000000 : ℝ), (1347884737/2500000000 : ℝ)] ![(43403356032741/100000000000000 : ℝ), (6169170348243/50000000000000 : ℝ), (44258303254019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328105463/2500000000 : ℝ)|^4229 ≤ (43403356032741/100000000000000 : ℝ)^3205
        have hw : |(1328105463/2500000000 : ℝ)|=(1328105463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047847843/10000000000 : ℝ)|^4229 ≤ (6169170348243/50000000000000 : ℝ)^3205
        have hw : |(-2047847843/10000000000 : ℝ)|=(2047847843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347884737/2500000000 : ℝ)|^4229 ≤ (44258303254019/100000000000000 : ℝ)^3205
        have hw : |(1347884737/2500000000 : ℝ)|=(1347884737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062484367/2000000000 : ℝ)*x 0 + (5391538961/10000000000 : ℝ)*x 1 + (-2047847849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062484367/2000000000 : ℝ)^4229 ≤ (169544358787/390625000000 : ℝ)^3205 := by
    have hnat : (1062484367 : ℕ)^4229*390625000000^3205 ≤ 169544358787^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062484367 2000000000 169544358787 390625000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391538961/10000000000 : ℝ)^4229 ≤ (4425830339483/10000000000000 : ℝ)^3205 := by
    have hnat : (5391538961 : ℕ)^4229*10000000000000^3205 ≤ 4425830339483^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391538961 10000000000 4425830339483 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047847849/10000000000 : ℝ)^4229 ≤ (6169170372093/50000000000000 : ℝ)^3205 := by
    have hnat : (2047847849 : ℕ)^4229*50000000000000^3205 ≤ 6169170372093^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047847849 10000000000 6169170372093 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062484367/2000000000 : ℝ), (5391538961/10000000000 : ℝ), (-2047847849/10000000000 : ℝ)] ![(169544358787/390625000000 : ℝ), (4425830339483/10000000000000 : ℝ), (6169170372093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062484367/2000000000 : ℝ)|^4229 ≤ (169544358787/390625000000 : ℝ)^3205
        have hw : |(1062484367/2000000000 : ℝ)|=(1062484367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391538961/10000000000 : ℝ)|^4229 ≤ (4425830339483/10000000000000 : ℝ)^3205
        have hw : |(5391538961/10000000000 : ℝ)|=(5391538961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2047847849/10000000000 : ℝ)|^4229 ≤ (6169170372093/50000000000000 : ℝ)^3205
        have hw : |(-2047847849/10000000000 : ℝ)|=(2047847849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s5_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086896043/2500000000 : ℝ)*x 0 + (4476468499/10000000000 : ℝ)*x 1 + (844462383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086896043/2500000000 : ℝ)^4229 ≤ (33317158312859/100000000000000 : ℝ)^3205 := by
    have hnat : (1086896043 : ℕ)^4229*100000000000000^3205 ≤ 33317158312859^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086896043 2500000000 33317158312859 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476468499/10000000000 : ℝ)^4229 ≤ (34626545227203/100000000000000 : ℝ)^3205 := by
    have hnat : (4476468499 : ℕ)^4229*100000000000000^3205 ≤ 34626545227203^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476468499 10000000000 34626545227203 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844462383/2000000000 : ℝ)^4229 ≤ (32056296447029/100000000000000 : ℝ)^3205 := by
    have hnat : (844462383 : ℕ)^4229*100000000000000^3205 ≤ 32056296447029^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844462383 2000000000 32056296447029 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086896043/2500000000 : ℝ), (4476468499/10000000000 : ℝ), (844462383/2000000000 : ℝ)] ![(33317158312859/100000000000000 : ℝ), (34626545227203/100000000000000 : ℝ), (32056296447029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086896043/2500000000 : ℝ)|^4229 ≤ (33317158312859/100000000000000 : ℝ)^3205
        have hw : |(1086896043/2500000000 : ℝ)|=(1086896043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476468499/10000000000 : ℝ)|^4229 ≤ (34626545227203/100000000000000 : ℝ)^3205
        have hw : |(4476468499/10000000000 : ℝ)|=(4476468499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844462383/2000000000 : ℝ)|^4229 ≤ (32056296447029/100000000000000 : ℝ)^3205
        have hw : |(844462383/2000000000 : ℝ)|=(844462383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2871/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (707/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11389/100000 : ℝ) ^ (8457/2048 : ℝ) ≤ (3175387830560461/25000000000000000000 : ℝ) := by
    have hpowers : (11389/100000 : ℝ)^8457 ≤ (3175387830560461/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11389 : ℕ)^8457*25000000000000000000^2048 ≤ 3175387830560461^2048*100000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11389 100000 3175387830560461 25000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11389/100000 : ℝ)) (X := (3175387830560461/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8457/2048 : ℝ) ≤ (31943524722506149/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8457 ≤ (31943524722506149/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8457*100000000000000000000^2048 ≤ 31943524722506149^2048*100000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 31943524722506149 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (31943524722506149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503175387830560461/12500000000000000000 : ℝ) ≤ (2500153779552903/2500000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (12503175387830560461/12500000000000000000 : ℝ)^2048 ≤ (2500153779552903/2500000000000000 : ℝ)^8457 := by
      have hnat : (12503175387830560461 : ℕ)^2048*2500000000000000^8457 ≤ 2500153779552903^8457*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503175387830560461 12500000000000000000 2500153779552903 2500000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500153779552903/2500000000000000 : ℝ)) (X := (12503175387830560461/12500000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044645076044747993/100000000000000000000 : ℝ) ≤ (10001080970228833/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (100044645076044747993/100000000000000000000 : ℝ)^2048 ≤ (10001080970228833/10000000000000000 : ℝ)^8457 := by
      have hnat : (100044645076044747993 : ℕ)^2048*10000000000000000^8457 ≤ 10001080970228833^8457*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044645076044747993 100000000000000000000 10001080970228833 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001080970228833/10000000000000000 : ℝ)) (X := (100044645076044747993/100000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031943524722506149/50000000000000000000 : ℝ) ≤ (5000773411123027/5000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50031943524722506149/50000000000000000000 : ℝ)^2048 ≤ (5000773411123027/5000000000000000 : ℝ)^8457 := by
      have hnat : (50031943524722506149 : ℕ)^2048*5000000000000000^8457 ≤ 5000773411123027^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031943524722506149 50000000000000000000 5000773411123027 5000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000773411123027/5000000000000000 : ℝ)) (X := (50031943524722506149/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3175387830560461/25000000000000000000 : ℝ) ≤ ((14245570954827417131/14250000000000000000 : ℝ)+2*(465852017221/285000000000000 : ℝ)*(11389/100000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (14245570954827417131/14250000000000000000 : ℝ)+2*(465852017221/285000000000000 : ℝ)*(11389/100000 : ℝ)=(2500153779552903/2500000000000000 : ℝ) by norm_num, show 1+2*(3175387830560461/25000000000000000000 : ℝ)=(12503175387830560461/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31943524722506149/100000000000000000000 : ℝ)+(3175387830560461/25000000000000000000 : ℝ) ≤ ((14245570954827417131/14250000000000000000 : ℝ)+(465852017221/285000000000000 : ℝ)*((14239/100000 : ℝ)+(11389/100000 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (14245570954827417131/14250000000000000000 : ℝ)+(465852017221/285000000000000 : ℝ)*((14239/100000 : ℝ)+(11389/100000 : ℝ))=(10001080970228833/10000000000000000 : ℝ) by norm_num, show 1+(31943524722506149/100000000000000000000 : ℝ)+(3175387830560461/25000000000000000000 : ℝ)=(100044645076044747993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31943524722506149/100000000000000000000 : ℝ) ≤ ((14245570954827417131/14250000000000000000 : ℝ)+2*(465852017221/285000000000000 : ℝ)*(14239/100000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (14245570954827417131/14250000000000000000 : ℝ)+2*(465852017221/285000000000000 : ℝ)*(14239/100000 : ℝ)=(5000773411123027/5000000000000000 : ℝ) by norm_num, show 1+2*(31943524722506149/100000000000000000000 : ℝ)=(50031943524722506149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14245570954827417131/14250000000000000000 : ℝ)*(X 1 0+X 2 0)+(465852017221/285000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (14245570954827417131/14250000000000000000 : ℝ)) (alpha := (465852017221/285000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14245570954827417131/14250000000000000000 : ℝ)*(X 0 1+X 2 1)+(465852017221/285000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (14245570954827417131/14250000000000000000 : ℝ)) (alpha := (465852017221/285000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14245570954827417131/14250000000000000000 : ℝ)*(X 0 2+X 1 2)+(465852017221/285000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (14245570954827417131/14250000000000000000 : ℝ)) (alpha := (465852017221/285000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527330929/2500000000 : ℝ)*X 0 0+(336991377/625000000 : ℝ)*X 0 1+(5266482761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068892367/2000000000 : ℝ)*X 1 0+(-543226037/2500000000 : ℝ)*X 1 1+(1316620691/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068892381/2000000000 : ℝ)*X 2 0+(1053296537/2000000000 : ℝ)*X 2 1+(-2172904159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347574437/10000000000 : ℝ)*X 0 0+(2110826791/5000000000 : ℝ)*X 0 1+(895424853/2000000000 : ℝ)*X 0 2+(4347574437/10000000000 : ℝ)*X 1 0+(2110826791/5000000000 : ℝ)*X 1 1+(895424853/2000000000 : ℝ)*X 1 2+(4347574437/10000000000 : ℝ)*X 2 0+(2110826791/5000000000 : ℝ)*X 2 1+(895424853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109328653/10000000000 : ℝ)*X 0 0+(526680461/1000000000 : ℝ)*X 0 1+(539153893/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328105463/2500000000 : ℝ)*X 1 0+(-2047847843/10000000000 : ℝ)*X 1 1+(1347884737/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062484367/2000000000 : ℝ)*X 2 0+(5391538961/10000000000 : ℝ)*X 2 1+(-2047847849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086896043/2500000000 : ℝ)*X 0 0+(4476468499/10000000000 : ℝ)*X 0 1+(844462383/2000000000 : ℝ)*X 0 2+(1086896043/2500000000 : ℝ)*X 1 0+(4476468499/10000000000 : ℝ)*X 1 1+(844462383/2000000000 : ℝ)*X 1 2+(1086896043/2500000000 : ℝ)*X 2 0+(4476468499/10000000000 : ℝ)*X 2 1+(844462383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (780661586436915441419151951/237500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414470051/100000000000000 : ℝ)*(base19) + (39480321/12500000000000 : ℝ)*(base23) + (128903153/100000000000000 : ℝ)*(lower2) + (29742371/20000000000000 : ℝ)*(upper3) + (20361397/100000000000000 : ℝ)*(lower4) + (5945079929686221/100000000000000 : ℝ)*(major0) + (5945079929686221/100000000000000 : ℝ)*(major1) + (5945079929686221/100000000000000 : ℝ)*(major2) + (7975807161943821/100000000000000 : ℝ)*(sp0) + (99697634192023/1250000000000 : ℝ)*(sp1) + (7975810833989323/100000000000000 : ℝ)*(sp2) + (1957171851715321/50000000000000 : ℝ)*(sp3) + (398788807/10000000000000 : ℝ)*(sp4) + (4896543361/100000000000000 : ℝ)*(sp7) + (978587149993501/25000000000000 : ℝ)*(f.failure) + (7975811149831891/100000000000000 : ℝ)*(f.sum) + (9425749671053/4750000000000000000000000000 : ℝ)*base66 + (469152886142367317/475000000000000000000000000000000 : ℝ)*base67 + (3031101960082632683/475000000000000000000000000000000 : ℝ)*base70 + (309407872917367317/475000000000000000000000000000000 : ℝ)*base71 + (10900068604697/4750000000000000000000000000 : ℝ)*base73 + (7414777627607632683/475000000000000000000000000000000 : ℝ)*base76 + (7839152486707632683/475000000000000000000000000000000 : ℝ)*base78 + (10953393123282632683/475000000000000000000000000000000 : ℝ)*base80 + (14863207614053/4750000000000000000000000000 : ℝ)*base82 + (3078291/625000000000000000000 : ℝ)*base89 + (3078291/625000000000000000000 : ℝ)*base91 + (3078291/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127952816785133332939403347/14843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (798204187/50000000000000 : ℝ)*(base19) + (106270823/6250000000000 : ℝ)*(base23) + (47386223/25000000000000 : ℝ)*(upper3) + (14928567/25000000000000 : ℝ)*(lower4) + (92886759/50000000000000 : ℝ)*(upper5) + (373488112796713/6250000000000 : ℝ)*(major0) + (373488112796713/6250000000000 : ℝ)*(major1) + (373488112796713/6250000000000 : ℝ)*(major2) + (44826600489/100000000000000 : ℝ)*(sp1) + (2979633753/6250000000000 : ℝ)*(sp2) + (4008518807166647/50000000000000 : ℝ)*(sp4) + (8016991191324431/100000000000000 : ℝ)*(sp5) + (8016988239860079/100000000000000 : ℝ)*(sp6) + (983645426957217/25000000000000 : ℝ)*(sp7) + (983645426957217/25000000000000 : ℝ)*(f.failure) + (4008518807166647/50000000000000 : ℝ)*(f.sum) + (16528835090333/3562500000000000000000000000 : ℝ)*base66 + (458571777222840403/89062500000000000000000000000000 : ℝ)*base67 + (1011045776322840403/89062500000000000000000000000000 : ℝ)*base69 + (328604132163097097/89062500000000000000000000000000 : ℝ)*base72 + (1242478014209/7125000000000000000000000000 : ℝ)*base73 + (3426708023904090403/89062500000000000000000000000000 : ℝ)*base75 + (127699314640027903/89062500000000000000000000000000 : ℝ)*base77 + (1256631383969347097/89062500000000000000000000000000 : ℝ)*base80 + (17191564877041/7125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4568353/625000000000000000000 : ℝ)*base90 + (4568353/625000000000000000000 : ℝ)*base92 + (4568353/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1265_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (707/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1265_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (707/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1265_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1265_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1265_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (707/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1265_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

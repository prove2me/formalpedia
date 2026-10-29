-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1702_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:55.669987+00:00
-- url     : https://prove2.me/submissions/768a385c-f23e-4553-8824-1ef93b619039

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
theorem support_rectangle_w1702_s3_0 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-720754973/5000000000 : ℝ)*x 0 + (1368801259/2500000000 : ℝ)*x 1 + (5137222827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (720754973/5000000000 : ℝ)^5239 ≤ (1800898434547/20000000000000 : ℝ)^4215 := by
    have hnat : (720754973 : ℕ)^5239*20000000000000^4215 ≤ 1800898434547^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720754973 5000000000 1800898434547 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368801259/2500000000 : ℝ)^5239 ≤ (11824611907543/25000000000000 : ℝ)^4215 := by
    have hnat : (1368801259 : ℕ)^5239*25000000000000^4215 ≤ 11824611907543^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368801259 2500000000 11824611907543 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137222827/10000000000 : ℝ)^5239 ≤ (21848530093567/50000000000000 : ℝ)^4215 := by
    have hnat : (5137222827 : ℕ)^5239*50000000000000^4215 ≤ 21848530093567^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137222827 10000000000 21848530093567 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-720754973/5000000000 : ℝ), (1368801259/2500000000 : ℝ), (5137222827/10000000000 : ℝ)] ![(1800898434547/20000000000000 : ℝ), (11824611907543/25000000000000 : ℝ), (21848530093567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-720754973/5000000000 : ℝ)|^5239 ≤ (1800898434547/20000000000000 : ℝ)^4215
        have hw : |(-720754973/5000000000 : ℝ)|=(720754973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368801259/2500000000 : ℝ)|^5239 ≤ (11824611907543/25000000000000 : ℝ)^4215
        have hw : |(1368801259/2500000000 : ℝ)|=(1368801259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137222827/10000000000 : ℝ)|^5239 ≤ (21848530093567/50000000000000 : ℝ)^4215
        have hw : |(5137222827/10000000000 : ℝ)|=(5137222827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_1 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336550897/2500000000 : ℝ)*x 0 + (-808441053/5000000000 : ℝ)*x 1 + (102744457/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336550897/2500000000 : ℝ)^5239 ≤ (2295865065419/5000000000000 : ℝ)^4215 := by
    have hnat : (1336550897 : ℕ)^5239*5000000000000^4215 ≤ 2295865065419^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336550897 2500000000 2295865065419 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808441053/5000000000 : ℝ)^5239 ≤ (10385638245471/100000000000000 : ℝ)^4215 := by
    have hnat : (808441053 : ℕ)^5239*100000000000000^4215 ≤ 10385638245471^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808441053 5000000000 10385638245471 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102744457/200000000 : ℝ)^5239 ≤ (436970604303/1000000000000 : ℝ)^4215 := by
    have hnat : (102744457 : ℕ)^5239*1000000000000^4215 ≤ 436970604303^4215*200000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102744457 200000000 436970604303 1000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336550897/2500000000 : ℝ), (-808441053/5000000000 : ℝ), (102744457/200000000 : ℝ)] ![(2295865065419/5000000000000 : ℝ), (10385638245471/100000000000000 : ℝ), (436970604303/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336550897/2500000000 : ℝ)|^5239 ≤ (2295865065419/5000000000000 : ℝ)^4215
        have hw : |(1336550897/2500000000 : ℝ)|=(1336550897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-808441053/5000000000 : ℝ)|^5239 ≤ (10385638245471/100000000000000 : ℝ)^4215
        have hw : |(-808441053/5000000000 : ℝ)|=(808441053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102744457/200000000 : ℝ)|^5239 ≤ (436970604303/1000000000000 : ℝ)^4215
        have hw : |(102744457/200000000 : ℝ)|=(102744457/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_2 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346203589/10000000000 : ℝ)*x 0 + (5137222873/10000000000 : ℝ)*x 1 + (-808441037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346203589/10000000000 : ℝ)^5239 ≤ (9183460263811/20000000000000 : ℝ)^4215 := by
    have hnat : (5346203589 : ℕ)^5239*20000000000000^4215 ≤ 9183460263811^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346203589 10000000000 9183460263811 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137222873/10000000000 : ℝ)^5239 ≤ (21848530336733/50000000000000 : ℝ)^4215 := by
    have hnat : (5137222873 : ℕ)^5239*50000000000000^4215 ≤ 21848530336733^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137222873 10000000000 21848530336733 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808441037/5000000000 : ℝ)^5239 ≤ (1298204748749/12500000000000 : ℝ)^4215 := by
    have hnat : (808441037 : ℕ)^5239*12500000000000^4215 ≤ 1298204748749^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808441037 5000000000 1298204748749 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346203589/10000000000 : ℝ), (5137222873/10000000000 : ℝ), (-808441037/5000000000 : ℝ)] ![(9183460263811/20000000000000 : ℝ), (21848530336733/50000000000000 : ℝ), (1298204748749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346203589/10000000000 : ℝ)|^5239 ≤ (9183460263811/20000000000000 : ℝ)^4215
        have hw : |(5346203589/10000000000 : ℝ)|=(5346203589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137222873/10000000000 : ℝ)|^5239 ≤ (21848530336733/50000000000000 : ℝ)^4215
        have hw : |(5137222873/10000000000 : ℝ)|=(5137222873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-808441037/5000000000 : ℝ)|^5239 ≤ (1298204748749/12500000000000 : ℝ)^4215
        have hw : |(-808441037/5000000000 : ℝ)|=(808441037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_3 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823022427/2000000000 : ℝ)*x 0 + (57066601/156250000 : ℝ)*x 1 + (36914303/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823022427/2000000000 : ℝ)^5239 ≤ (33166438259871/100000000000000 : ℝ)^4215 := by
    have hnat : (823022427 : ℕ)^5239*100000000000000^4215 ≤ 33166438259871^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823022427 2000000000 33166438259871 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57066601/156250000 : ℝ)^5239 ≤ (28594991209711/100000000000000 : ℝ)^4215 := by
    have hnat : (57066601 : ℕ)^5239*100000000000000^4215 ≤ 28594991209711^4215*156250000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57066601 156250000 28594991209711 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36914303/80000000 : ℝ)^5239 ≤ (149369416051/390625000000 : ℝ)^4215 := by
    have hnat : (36914303 : ℕ)^5239*390625000000^4215 ≤ 149369416051^4215*80000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36914303 80000000 149369416051 390625000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823022427/2000000000 : ℝ), (57066601/156250000 : ℝ), (36914303/80000000 : ℝ)] ![(33166438259871/100000000000000 : ℝ), (28594991209711/100000000000000 : ℝ), (149369416051/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823022427/2000000000 : ℝ)|^5239 ≤ (33166438259871/100000000000000 : ℝ)^4215
        have hw : |(823022427/2000000000 : ℝ)|=(823022427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57066601/156250000 : ℝ)|^5239 ≤ (28594991209711/100000000000000 : ℝ)^4215
        have hw : |(57066601/156250000 : ℝ)|=(57066601/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36914303/80000000 : ℝ)|^5239 ≤ (149369416051/390625000000 : ℝ)^4215
        have hw : |(36914303/80000000 : ℝ)|=(36914303/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_4 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1441664673/10000000000 : ℝ)*x 0 + (5140939781/10000000000 : ℝ)*x 1 + (2735716327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1441664673/10000000000 : ℝ)^5239 ≤ (9005693507841/100000000000000 : ℝ)^4215 := by
    have hnat : (1441664673 : ℕ)^5239*100000000000000^4215 ≤ 9005693507841^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441664673 10000000000 9005693507841 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140939781/10000000000 : ℝ)^5239 ≤ (1093409021493/2500000000000 : ℝ)^4215 := by
    have hnat : (5140939781 : ℕ)^5239*2500000000000^4215 ≤ 1093409021493^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140939781 10000000000 1093409021493 2500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735716327/5000000000 : ℝ)^5239 ≤ (23628972807683/50000000000000 : ℝ)^4215 := by
    have hnat : (2735716327 : ℕ)^5239*50000000000000^4215 ≤ 23628972807683^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735716327 5000000000 23628972807683 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1441664673/10000000000 : ℝ), (5140939781/10000000000 : ℝ), (2735716327/5000000000 : ℝ)] ![(9005693507841/100000000000000 : ℝ), (1093409021493/2500000000000 : ℝ), (23628972807683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1441664673/10000000000 : ℝ)|^5239 ≤ (9005693507841/100000000000000 : ℝ)^4215
        have hw : |(-1441664673/10000000000 : ℝ)|=(1441664673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140939781/10000000000 : ℝ)|^5239 ≤ (1093409021493/2500000000000 : ℝ)^4215
        have hw : |(5140939781/10000000000 : ℝ)|=(5140939781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735716327/5000000000 : ℝ)|^5239 ≤ (23628972807683/50000000000000 : ℝ)^4215
        have hw : |(2735716327/5000000000 : ℝ)|=(2735716327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_5 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41060647/78125000 : ℝ)*x 0 + (-1282672319/10000000000 : ℝ)*x 1 + (5471432657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41060647/78125000 : ℝ)^5239 ≤ (44953807905147/100000000000000 : ℝ)^4215 := by
    have hnat : (41060647 : ℕ)^5239*100000000000000^4215 ≤ 44953807905147^4215*78125000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41060647 78125000 44953807905147 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282672319/10000000000 : ℝ)^5239 ≤ (7788246425439/100000000000000 : ℝ)^4215 := by
    have hnat : (1282672319 : ℕ)^5239*100000000000000^4215 ≤ 7788246425439^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282672319 10000000000 7788246425439 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471432657/10000000000 : ℝ)^5239 ≤ (47257945647573/100000000000000 : ℝ)^4215 := by
    have hnat : (5471432657 : ℕ)^5239*100000000000000^4215 ≤ 47257945647573^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471432657 10000000000 47257945647573 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41060647/78125000 : ℝ), (-1282672319/10000000000 : ℝ), (5471432657/10000000000 : ℝ)] ![(44953807905147/100000000000000 : ℝ), (7788246425439/100000000000000 : ℝ), (47257945647573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41060647/78125000 : ℝ)|^5239 ≤ (44953807905147/100000000000000 : ℝ)^4215
        have hw : |(41060647/78125000 : ℝ)|=(41060647/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1282672319/10000000000 : ℝ)|^5239 ≤ (7788246425439/100000000000000 : ℝ)^4215
        have hw : |(-1282672319/10000000000 : ℝ)|=(1282672319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471432657/10000000000 : ℝ)|^5239 ≤ (47257945647573/100000000000000 : ℝ)^4215
        have hw : |(5471432657/10000000000 : ℝ)|=(5471432657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_6 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255762817/10000000000 : ℝ)*x 0 + (2735716331/5000000000 : ℝ)*x 1 + (-160334039/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255762817/10000000000 : ℝ)^5239 ≤ (22476903957889/50000000000000 : ℝ)^4215 := by
    have hnat : (5255762817 : ℕ)^5239*50000000000000^4215 ≤ 22476903957889^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255762817 10000000000 22476903957889 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735716331/5000000000 : ℝ)^5239 ≤ (47257945701251/100000000000000 : ℝ)^4215 := by
    have hnat : (2735716331 : ℕ)^5239*100000000000000^4215 ≤ 47257945701251^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735716331 5000000000 47257945701251 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160334039/1250000000 : ℝ)^5239 ≤ (778824637261/10000000000000 : ℝ)^4215 := by
    have hnat : (160334039 : ℕ)^5239*10000000000000^4215 ≤ 778824637261^4215*1250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160334039 1250000000 778824637261 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255762817/10000000000 : ℝ), (2735716331/5000000000 : ℝ), (-160334039/1250000000 : ℝ)] ![(22476903957889/50000000000000 : ℝ), (47257945701251/100000000000000 : ℝ), (778824637261/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255762817/10000000000 : ℝ)|^5239 ≤ (22476903957889/50000000000000 : ℝ)^4215
        have hw : |(5255762817/10000000000 : ℝ)|=(5255762817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735716331/5000000000 : ℝ)|^5239 ≤ (47257945701251/100000000000000 : ℝ)^4215
        have hw : |(2735716331/5000000000 : ℝ)|=(2735716331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-160334039/1250000000 : ℝ)|^5239 ≤ (778824637261/10000000000000 : ℝ)^4215
        have hw : |(-160334039/1250000000 : ℝ)|=(160334039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s3_7 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4115552669/10000000000 : ℝ)*x 0 + (4603708153/10000000000 : ℝ)*x 1 + (3663000087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4115552669/10000000000 : ℝ)^5239 ≤ (33170851454291/100000000000000 : ℝ)^4215 := by
    have hnat : (4115552669 : ℕ)^5239*100000000000000^4215 ≤ 33170851454291^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115552669 10000000000 33170851454291 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4603708153/10000000000 : ℝ)^5239 ≤ (38129627091317/100000000000000 : ℝ)^4215 := by
    have hnat : (4603708153 : ℕ)^5239*100000000000000^4215 ≤ 38129627091317^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603708153 10000000000 38129627091317 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3663000087/10000000000 : ℝ)^5239 ≤ (14349760720697/50000000000000 : ℝ)^4215 := by
    have hnat : (3663000087 : ℕ)^5239*50000000000000^4215 ≤ 14349760720697^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663000087 10000000000 14349760720697 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4115552669/10000000000 : ℝ), (4603708153/10000000000 : ℝ), (3663000087/10000000000 : ℝ)] ![(33170851454291/100000000000000 : ℝ), (38129627091317/100000000000000 : ℝ), (14349760720697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4115552669/10000000000 : ℝ)|^5239 ≤ (33170851454291/100000000000000 : ℝ)^4215
        have hw : |(4115552669/10000000000 : ℝ)|=(4115552669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4603708153/10000000000 : ℝ)|^5239 ≤ (38129627091317/100000000000000 : ℝ)^4215
        have hw : |(4603708153/10000000000 : ℝ)|=(4603708153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3663000087/10000000000 : ℝ)|^5239 ≤ (14349760720697/50000000000000 : ℝ)^4215
        have hw : |(3663000087/10000000000 : ℝ)|=(3663000087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1702_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9943/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (343/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3433/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (993/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3433/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (993/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3433/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (993/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3433/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (993/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3433/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (993/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3433/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (993/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (993/10000 : ℝ) ^ (5231/1024 : ℝ) ≤ (751652503486429/100000000000000000000 : ℝ) := by
    have hpowers : (993/10000 : ℝ)^5231 ≤ (751652503486429/100000000000000000000 : ℝ)^1024 := by
      have hnat : (993 : ℕ)^5231*100000000000000000000^1024 ≤ 751652503486429^1024*10000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        993 10000 751652503486429 100000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (993/10000 : ℝ)) (X := (751652503486429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3433/20000 : ℝ) ^ (5231/1024 : ℝ) ≤ (1538741392083979/12500000000000000000 : ℝ) := by
    have hpowers : (3433/20000 : ℝ)^5231 ≤ (1538741392083979/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3433 : ℕ)^5231*12500000000000000000^1024 ≤ 1538741392083979^1024*20000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3433 20000 1538741392083979 12500000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3433/20000 : ℝ)) (X := (1538741392083979/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000751652503486429/50000000000000000000 : ℝ) ≤ (10000029427930061/10000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (50000751652503486429/50000000000000000000 : ℝ)^1024 ≤ (10000029427930061/10000000000000000 : ℝ)^5231 := by
      have hnat : (50000751652503486429 : ℕ)^1024*10000000000000000^5231 ≤ 10000029427930061^5231*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000751652503486429 50000000000000000000 10000029427930061 10000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000029427930061/10000000000000000 : ℝ)) (X := (50000751652503486429/50000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013061583640158261/100000000000000000000 : ℝ) ≤ (10000255674999001/10000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (100013061583640158261/100000000000000000000 : ℝ)^1024 ≤ (10000255674999001/10000000000000000 : ℝ)^5231 := by
      have hnat : (100013061583640158261 : ℕ)^1024*10000000000000000^5231 ≤ 10000255674999001^5231*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013061583640158261 100000000000000000000 10000255674999001 10000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000255674999001/10000000000000000 : ℝ)) (X := (100013061583640158261/100000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251538741392083979/6250000000000000000 : ℝ) ≤ (10000481922067941/10000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (6251538741392083979/6250000000000000000 : ℝ)^1024 ≤ (10000481922067941/10000000000000000 : ℝ)^5231 := by
      have hnat : (6251538741392083979 : ℕ)^1024*10000000000000000^5231 ≤ 10000481922067941^5231*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251538741392083979 6250000000000000000 10000481922067941 10000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000481922067941/10000000000000000 : ℝ)) (X := (6251538741392083979/6250000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(751652503486429/100000000000000000000 : ℝ) ≤ ((14469143928856968587/14470000000000000000 : ℝ)+2*(11312353447/36175000000000 : ℝ)*(993/10000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (14469143928856968587/14470000000000000000 : ℝ)+2*(11312353447/36175000000000 : ℝ)*(993/10000 : ℝ)=(10000029427930061/10000000000000000 : ℝ) by norm_num, show 1+2*(751652503486429/100000000000000000000 : ℝ)=(50000751652503486429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1538741392083979/12500000000000000000 : ℝ)+(751652503486429/100000000000000000000 : ℝ) ≤ ((14469143928856968587/14470000000000000000 : ℝ)+(11312353447/36175000000000 : ℝ)*((3433/20000 : ℝ)+(993/10000 : ℝ)))^(5231/1024 : ℝ) := by
    rw [show (14469143928856968587/14470000000000000000 : ℝ)+(11312353447/36175000000000 : ℝ)*((3433/20000 : ℝ)+(993/10000 : ℝ))=(10000255674999001/10000000000000000 : ℝ) by norm_num, show 1+(1538741392083979/12500000000000000000 : ℝ)+(751652503486429/100000000000000000000 : ℝ)=(100013061583640158261/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1538741392083979/12500000000000000000 : ℝ) ≤ ((14469143928856968587/14470000000000000000 : ℝ)+2*(11312353447/36175000000000 : ℝ)*(3433/20000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (14469143928856968587/14470000000000000000 : ℝ)+2*(11312353447/36175000000000 : ℝ)*(3433/20000 : ℝ)=(10000481922067941/10000000000000000 : ℝ) by norm_num, show 1+2*(1538741392083979/12500000000000000000 : ℝ)=(6251538741392083979/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14469143928856968587/14470000000000000000 : ℝ)*(X 1 0+X 2 0)+(11312353447/36175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (993/10000 : ℝ)) (hi := (3433/20000 : ℝ)) (c := (14469143928856968587/14470000000000000000 : ℝ)) (alpha := (11312353447/36175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14469143928856968587/14470000000000000000 : ℝ)*(X 0 1+X 2 1)+(11312353447/36175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (993/10000 : ℝ)) (hi := (3433/20000 : ℝ)) (c := (14469143928856968587/14470000000000000000 : ℝ)) (alpha := (11312353447/36175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14469143928856968587/14470000000000000000 : ℝ)*(X 0 2+X 1 2)+(11312353447/36175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (993/10000 : ℝ)) (hi := (3433/20000 : ℝ)) (c := (14469143928856968587/14470000000000000000 : ℝ)) (alpha := (11312353447/36175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-720754973/5000000000 : ℝ)*X 0 0+(1368801259/2500000000 : ℝ)*X 0 1+(5137222827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336550897/2500000000 : ℝ)*X 1 0+(-808441053/5000000000 : ℝ)*X 1 1+(102744457/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346203589/10000000000 : ℝ)*X 2 0+(5137222873/10000000000 : ℝ)*X 2 1+(-808441037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((823022427/2000000000 : ℝ)*X 0 0+(57066601/156250000 : ℝ)*X 0 1+(36914303/80000000 : ℝ)*X 0 2+(823022427/2000000000 : ℝ)*X 1 0+(57066601/156250000 : ℝ)*X 1 1+(36914303/80000000 : ℝ)*X 1 2+(823022427/2000000000 : ℝ)*X 2 0+(57066601/156250000 : ℝ)*X 2 1+(36914303/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1441664673/10000000000 : ℝ)*X 0 0+(5140939781/10000000000 : ℝ)*X 0 1+(2735716327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41060647/78125000 : ℝ)*X 1 0+(-1282672319/10000000000 : ℝ)*X 1 1+(5471432657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255762817/10000000000 : ℝ)*X 2 0+(2735716331/5000000000 : ℝ)*X 2 1+(-160334039/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4115552669/10000000000 : ℝ)*X 0 0+(4603708153/10000000000 : ℝ)*X 0 1+(3663000087/10000000000 : ℝ)*X 0 2+(4115552669/10000000000 : ℝ)*X 1 0+(4603708153/10000000000 : ℝ)*X 1 1+(3663000087/10000000000 : ℝ)*X 1 2+(4115552669/10000000000 : ℝ)*X 2 0+(4603708153/10000000000 : ℝ)*X 2 1+(3663000087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7121843310667630510259123931/723500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187783823/12500000000000 : ℝ)*(base19) + (1435535781/100000000000000 : ℝ)*(base23) + (1798683/5000000000000 : ℝ)*(lower2) + (57604333/25000000000000 : ℝ)*(upper3) + (202172641/100000000000000 : ℝ)*(upper5) + (1999125049256343/100000000000000 : ℝ)*(major0) + (1999125049256343/100000000000000 : ℝ)*(major1) + (1999125049256343/100000000000000 : ℝ)*(major2) + (2958750526099273/100000000000000 : ℝ)*(sp0) + (295876419120243/10000000000000 : ℝ)*(sp1) + (184922766121077/6250000000000 : ℝ)*(sp2) + (1039478629203667/100000000000000 : ℝ)*(sp3) + (15167373741/100000000000000 : ℝ)*(sp4) + (5447716059/100000000000000 : ℝ)*(sp7) + (519742038459863/50000000000000 : ℝ)*(f.failure) + (1479382846736507/50000000000000 : ℝ)*(f.sum) + (16324542845491/7235000000000000000000000000 : ℝ)*base66 + (3713946932781897341/1447000000000000000000000000000000 : ℝ)*base67 + (13587024610468897341/1447000000000000000000000000000000 : ℝ)*base69 + (8462544705257897341/1447000000000000000000000000000000 : ℝ)*base71 + (7081666617441/7235000000000000000000000000 : ℝ)*base74 + (5023270390063897341/1447000000000000000000000000000000 : ℝ)*base75 + (5344539254081897341/1447000000000000000000000000000000 : ℝ)*base77 + (14332788285592897341/1447000000000000000000000000000000 : ℝ)*base79 + (13019760981817/3617500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1447673/625000000000000000000 : ℝ)*base89 + (1447673/625000000000000000000 : ℝ)*base91 + (1447673/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1350004439364603316792502109/180875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513092211/50000000000000 : ℝ)*(base19) + (1110611899/100000000000000 : ℝ)*(base23) + (2462093/800000000000 : ℝ)*(lower1) + (78930319/50000000000000 : ℝ)*(upper3) + (2329809/6250000000000 : ℝ)*(lower4) + (19548931/12500000000000 : ℝ)*(upper5) + (1022199992281331/50000000000000 : ℝ)*(major0) + (1022199992281331/50000000000000 : ℝ)*(major1) + (1022199992281331/50000000000000 : ℝ)*(major2) + (150232459/20000000000000 : ℝ)*(sp2) + (3025774057382813/100000000000000 : ℝ)*(sp4) + (378221628899799/12500000000000 : ℝ)*(sp5) + (3025772195608619/100000000000000 : ℝ)*(sp6) + (1063025662951073/100000000000000 : ℝ)*(sp7) + (1063025662951073/100000000000000 : ℝ)*(f.failure) + (3025774057382813/100000000000000 : ℝ)*(f.sum) + (1141033596997/904375000000000000000000000 : ℝ)*base65 + (4873426385049349297/723500000000000000000000000000000 : ℝ)*base67 + (3100800284529150703/723500000000000000000000000000000 : ℝ)*base70 + (82042968394854849297/723500000000000000000000000000000 : ℝ)*base71 + (27704938463221/7235000000000000000000000000 : ℝ)*base73 + (26556830797783849297/723500000000000000000000000000000 : ℝ)*base75 + (1529859262413849297/723500000000000000000000000000000 : ℝ)*base77 + (1923642104089349297/723500000000000000000000000000000 : ℝ)*base79 + (16075488269699/7235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (768417/1250000000000000000000 : ℝ)*base90 + (768417/1250000000000000000000 : ℝ)*base92 + (768417/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1702_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (343/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1702_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1702_s4_0 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-720758629/5000000000 : ℝ)*x 0 + (5475178363/10000000000 : ℝ)*x 1 + (1027448909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (720758629/5000000000 : ℝ)^5239 ≤ (9004548944037/100000000000000 : ℝ)^4215 := by
    have hnat : (720758629 : ℕ)^5239*100000000000000^4215 ≤ 9004548944037^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720758629 5000000000 9004548944037 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475178363/10000000000 : ℝ)^5239 ≤ (47298161232867/100000000000000 : ℝ)^4215 := by
    have hnat : (5475178363 : ℕ)^5239*100000000000000^4215 ≤ 47298161232867^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475178363 10000000000 47298161232867 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027448909/2000000000 : ℝ)^5239 ≤ (4369728979919/10000000000000 : ℝ)^4215 := by
    have hnat : (1027448909 : ℕ)^5239*10000000000000^4215 ≤ 4369728979919^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027448909 2000000000 4369728979919 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-720758629/5000000000 : ℝ), (5475178363/10000000000 : ℝ), (1027448909/2000000000 : ℝ)] ![(9004548944037/100000000000000 : ℝ), (47298161232867/100000000000000 : ℝ), (4369728979919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-720758629/5000000000 : ℝ)|^5239 ≤ (9004548944037/100000000000000 : ℝ)^4215
        have hw : |(-720758629/5000000000 : ℝ)|=(720758629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475178363/10000000000 : ℝ)|^5239 ≤ (47298161232867/100000000000000 : ℝ)^4215
        have hw : |(5475178363/10000000000 : ℝ)|=(5475178363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027448909/2000000000 : ℝ)|^5239 ≤ (4369728979919/10000000000000 : ℝ)^4215
        have hw : |(1027448909/2000000000 : ℝ)|=(1027448909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_1 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673098571/5000000000 : ℝ)*x 0 + (-404215141/2500000000 : ℝ)*x 1 + (2568622813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673098571/5000000000 : ℝ)^5239 ≤ (22958616247577/50000000000000 : ℝ)^4215 := by
    have hnat : (2673098571 : ℕ)^5239*50000000000000^4215 ≤ 22958616247577^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673098571 5000000000 22958616247577 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404215141/2500000000 : ℝ)^5239 ≤ (10385466260311/100000000000000 : ℝ)^4215 := by
    have hnat : (404215141 : ℕ)^5239*100000000000000^4215 ≤ 10385466260311^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404215141 2500000000 10385466260311 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568622813/5000000000 : ℝ)^5239 ≤ (21848650613997/50000000000000 : ℝ)^4215 := by
    have hnat : (2568622813 : ℕ)^5239*50000000000000^4215 ≤ 21848650613997^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568622813 5000000000 21848650613997 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673098571/5000000000 : ℝ), (-404215141/2500000000 : ℝ), (2568622813/5000000000 : ℝ)] ![(22958616247577/50000000000000 : ℝ), (10385466260311/100000000000000 : ℝ), (21848650613997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673098571/5000000000 : ℝ)|^5239 ≤ (22958616247577/50000000000000 : ℝ)^4215
        have hw : |(2673098571/5000000000 : ℝ)|=(2673098571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404215141/2500000000 : ℝ)|^5239 ≤ (10385466260311/100000000000000 : ℝ)^4215
        have hw : |(-404215141/2500000000 : ℝ)|=(404215141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568622813/5000000000 : ℝ)|^5239 ≤ (21848650613997/50000000000000 : ℝ)^4215
        have hw : |(2568622813/5000000000 : ℝ)|=(2568622813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_2 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133654899/250000000 : ℝ)*x 0 + (2568623347/5000000000 : ℝ)*x 1 + (-161686073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133654899/250000000 : ℝ)^5239 ≤ (45917219876907/100000000000000 : ℝ)^4215 := by
    have hnat : (133654899 : ℕ)^5239*100000000000000^4215 ≤ 45917219876907^4215*250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133654899 250000000 45917219876907 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568623347/5000000000 : ℝ)^5239 ≤ (43697312519357/100000000000000 : ℝ)^4215 := by
    have hnat : (2568623347 : ℕ)^5239*100000000000000^4215 ≤ 43697312519357^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568623347 5000000000 43697312519357 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161686073/1000000000 : ℝ)^5239 ≤ (5192733792803/50000000000000 : ℝ)^4215 := by
    have hnat : (161686073 : ℕ)^5239*50000000000000^4215 ≤ 5192733792803^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161686073 1000000000 5192733792803 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133654899/250000000 : ℝ), (2568623347/5000000000 : ℝ), (-161686073/1000000000 : ℝ)] ![(45917219876907/100000000000000 : ℝ), (43697312519357/100000000000000 : ℝ), (5192733792803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133654899/250000000 : ℝ)|^5239 ≤ (45917219876907/100000000000000 : ℝ)^4215
        have hw : |(133654899/250000000 : ℝ)|=(133654899/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568623347/5000000000 : ℝ)|^5239 ≤ (43697312519357/100000000000000 : ℝ)^4215
        have hw : |(2568623347/5000000000 : ℝ)|=(2568623347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-161686073/1000000000 : ℝ)|^5239 ≤ (5192733792803/50000000000000 : ℝ)^4215
        have hw : |(-161686073/1000000000 : ℝ)|=(161686073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_3 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823022789/2000000000 : ℝ)*x 0 + (3652337663/10000000000 : ℝ)*x 1 + (1153553767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823022789/2000000000 : ℝ)^5239 ≤ (33166456391907/100000000000000 : ℝ)^4215 := by
    have hnat : (823022789 : ℕ)^5239*100000000000000^4215 ≤ 33166456391907^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823022789 2000000000 33166456391907 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3652337663/10000000000 : ℝ)^5239 ≤ (14297861504479/50000000000000 : ℝ)^4215 := by
    have hnat : (3652337663 : ℕ)^5239*50000000000000^4215 ≤ 14297861504479^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3652337663 10000000000 14297861504479 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153553767/2500000000 : ℝ)^5239 ≤ (38237820580163/100000000000000 : ℝ)^4215 := by
    have hnat : (1153553767 : ℕ)^5239*100000000000000^4215 ≤ 38237820580163^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153553767 2500000000 38237820580163 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823022789/2000000000 : ℝ), (3652337663/10000000000 : ℝ), (1153553767/2500000000 : ℝ)] ![(33166456391907/100000000000000 : ℝ), (14297861504479/50000000000000 : ℝ), (38237820580163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823022789/2000000000 : ℝ)|^5239 ≤ (33166456391907/100000000000000 : ℝ)^4215
        have hw : |(823022789/2000000000 : ℝ)|=(823022789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3652337663/10000000000 : ℝ)|^5239 ≤ (14297861504479/50000000000000 : ℝ)^4215
        have hw : |(3652337663/10000000000 : ℝ)|=(3652337663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1153553767/2500000000 : ℝ)|^5239 ≤ (38237820580163/100000000000000 : ℝ)^4215
        have hw : |(1153553767/2500000000 : ℝ)|=(1153553767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_4 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360418003/2500000000 : ℝ)*x 0 + (1285240501/2500000000 : ℝ)*x 1 + (5471405457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360418003/2500000000 : ℝ)^5239 ≤ (450287524513/5000000000000 : ℝ)^4215 := by
    have hnat : (360418003 : ℕ)^5239*5000000000000^4215 ≤ 450287524513^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360418003 2500000000 450287524513 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285240501/2500000000 : ℝ)^5239 ≤ (2733537240759/6250000000000 : ℝ)^4215 := by
    have hnat : (1285240501 : ℕ)^5239*6250000000000^4215 ≤ 2733537240759^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285240501 2500000000 2733537240759 6250000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471405457/10000000000 : ℝ)^5239 ≤ (47257653640587/100000000000000 : ℝ)^4215 := by
    have hnat : (5471405457 : ℕ)^5239*100000000000000^4215 ≤ 47257653640587^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471405457 10000000000 47257653640587 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360418003/2500000000 : ℝ), (1285240501/2500000000 : ℝ), (5471405457/10000000000 : ℝ)] ![(450287524513/5000000000000 : ℝ), (2733537240759/6250000000000 : ℝ), (47257653640587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360418003/2500000000 : ℝ)|^5239 ≤ (450287524513/5000000000000 : ℝ)^4215
        have hw : |(-360418003/2500000000 : ℝ)|=(360418003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285240501/2500000000 : ℝ)|^5239 ≤ (2733537240759/6250000000000 : ℝ)^4215
        have hw : |(1285240501/2500000000 : ℝ)|=(1285240501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471405457/10000000000 : ℝ)|^5239 ≤ (47257653640587/100000000000000 : ℝ)^4215
        have hw : |(5471405457/10000000000 : ℝ)|=(5471405457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_5 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627884537/5000000000 : ℝ)*x 0 + (-641351283/5000000000 : ℝ)*x 1 + (5471405197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627884537/5000000000 : ℝ)^5239 ≤ (44953874435093/100000000000000 : ℝ)^4215 := by
    have hnat : (2627884537 : ℕ)^5239*100000000000000^4215 ≤ 44953874435093^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627884537 5000000000 44953874435093 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641351283/5000000000 : ℝ)^5239 ≤ (7788474700429/100000000000000 : ℝ)^4215 := by
    have hnat : (641351283 : ℕ)^5239*100000000000000^4215 ≤ 7788474700429^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641351283 5000000000 7788474700429 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471405197/10000000000 : ℝ)^5239 ≤ (9451530169869/20000000000000 : ℝ)^4215 := by
    have hnat : (5471405197 : ℕ)^5239*20000000000000^4215 ≤ 9451530169869^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471405197 10000000000 9451530169869 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627884537/5000000000 : ℝ), (-641351283/5000000000 : ℝ), (5471405197/10000000000 : ℝ)] ![(44953874435093/100000000000000 : ℝ), (7788474700429/100000000000000 : ℝ), (9451530169869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627884537/5000000000 : ℝ)|^5239 ≤ (44953874435093/100000000000000 : ℝ)^4215
        have hw : |(2627884537/5000000000 : ℝ)|=(2627884537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-641351283/5000000000 : ℝ)|^5239 ≤ (7788474700429/100000000000000 : ℝ)^4215
        have hw : |(-641351283/5000000000 : ℝ)|=(641351283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471405197/10000000000 : ℝ)|^5239 ≤ (9451530169869/20000000000000 : ℝ)^4215
        have hw : |(5471405197/10000000000 : ℝ)|=(5471405197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_6 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255769059/10000000000 : ℝ)*x 0 + (341962829/625000000 : ℝ)*x 1 + (-1282702493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255769059/10000000000 : ℝ)^5239 ≤ (71926198841/160000000000 : ℝ)^4215 := by
    have hnat : (5255769059 : ℕ)^5239*160000000000^4215 ≤ 71926198841^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255769059 10000000000 71926198841 160000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341962829/625000000 : ℝ)^5239 ≤ (47257651568627/100000000000000 : ℝ)^4215 := by
    have hnat : (341962829 : ℕ)^5239*100000000000000^4215 ≤ 47257651568627^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341962829 625000000 47257651568627 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282702493/10000000000 : ℝ)^5239 ≤ (3894237074747/50000000000000 : ℝ)^4215 := by
    have hnat : (1282702493 : ℕ)^5239*50000000000000^4215 ≤ 3894237074747^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282702493 10000000000 3894237074747 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255769059/10000000000 : ℝ), (341962829/625000000 : ℝ), (-1282702493/10000000000 : ℝ)] ![(71926198841/160000000000 : ℝ), (47257651568627/100000000000000 : ℝ), (3894237074747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255769059/10000000000 : ℝ)|^5239 ≤ (71926198841/160000000000 : ℝ)^4215
        have hw : |(5255769059/10000000000 : ℝ)|=(5255769059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341962829/625000000 : ℝ)|^5239 ≤ (47257651568627/100000000000000 : ℝ)^4215
        have hw : |(341962829/625000000 : ℝ)|=(341962829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1282702493/10000000000 : ℝ)|^5239 ≤ (3894237074747/50000000000000 : ℝ)^4215
        have hw : |(-1282702493/10000000000 : ℝ)|=(1282702493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s4_7 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4115557729/10000000000 : ℝ)*x 0 + (4603636879/10000000000 : ℝ)*x 1 + (146522809/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4115557729/10000000000 : ℝ)^5239 ≤ (16585451072587/50000000000000 : ℝ)^4215 := by
    have hnat : (4115557729 : ℕ)^5239*50000000000000^4215 ≤ 16585451072587^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115557729 10000000000 16585451072587 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4603636879/10000000000 : ℝ)^5239 ≤ (19064446680969/50000000000000 : ℝ)^4215 := by
    have hnat : (4603636879 : ℕ)^5239*50000000000000^4215 ≤ 19064446680969^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603636879 10000000000 19064446680969 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146522809/400000000 : ℝ)^5239 ≤ (5740040895271/20000000000000 : ℝ)^4215 := by
    have hnat : (146522809 : ℕ)^5239*20000000000000^4215 ≤ 5740040895271^4215*400000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146522809 400000000 5740040895271 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4115557729/10000000000 : ℝ), (4603636879/10000000000 : ℝ), (146522809/400000000 : ℝ)] ![(16585451072587/50000000000000 : ℝ), (19064446680969/50000000000000 : ℝ), (5740040895271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4115557729/10000000000 : ℝ)|^5239 ≤ (16585451072587/50000000000000 : ℝ)^4215
        have hw : |(4115557729/10000000000 : ℝ)|=(4115557729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4603636879/10000000000 : ℝ)|^5239 ≤ (19064446680969/50000000000000 : ℝ)^4215
        have hw : |(4603636879/10000000000 : ℝ)|=(4603636879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146522809/400000000 : ℝ)|^5239 ≤ (5740040895271/20000000000000 : ℝ)^4215
        have hw : |(146522809/400000000 : ℝ)|=(146522809/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1702_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1243/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17149/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (343/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (343/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (343/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (343/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (343/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (343/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9943/100000 : ℝ) ^ (5231/1024 : ℝ) ≤ (756692891035997/100000000000000000000 : ℝ) := by
    have hpowers : (9943/100000 : ℝ)^5231 ≤ (756692891035997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9943 : ℕ)^5231*100000000000000000000^1024 ≤ 756692891035997^1024*100000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9943 100000 756692891035997 100000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9943/100000 : ℝ)) (X := (756692891035997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (343/2000 : ℝ) ^ (5231/1024 : ℝ) ≤ (6127538572269047/50000000000000000000 : ℝ) := by
    have hpowers : (343/2000 : ℝ)^5231 ≤ (6127538572269047/50000000000000000000 : ℝ)^1024 := by
      have hnat : (343 : ℕ)^5231*50000000000000000000^1024 ≤ 6127538572269047^1024*2000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 2000 6127538572269047 50000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/2000 : ℝ)) (X := (6127538572269047/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000756692891035997/50000000000000000000 : ℝ) ≤ (5000014812632479/5000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (50000756692891035997/50000000000000000000 : ℝ)^1024 ≤ (5000014812632479/5000000000000000 : ℝ)^5231 := by
      have hnat : (50000756692891035997 : ℕ)^1024*5000000000000000^5231 ≤ 5000014812632479^5231*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000756692891035997 50000000000000000000 5000014812632479 5000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000014812632479/5000000000000000 : ℝ)) (X := (50000756692891035997/50000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013011770035574091/100000000000000000000 : ℝ) ≤ (10000254699969683/10000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (100013011770035574091/100000000000000000000 : ℝ)^1024 ≤ (10000254699969683/10000000000000000 : ℝ)^5231 := by
      have hnat : (100013011770035574091 : ℕ)^1024*10000000000000000^5231 ≤ 10000254699969683^5231*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013011770035574091 100000000000000000000 10000254699969683 10000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000254699969683/10000000000000000 : ℝ)) (X := (100013011770035574091/100000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006127538572269047/25000000000000000000 : ℝ) ≤ (1250059971834301/1250000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (25006127538572269047/25000000000000000000 : ℝ)^1024 ≤ (1250059971834301/1250000000000000 : ℝ)^5231 := by
      have hnat : (25006127538572269047 : ℕ)^1024*1250000000000000^5231 ≤ 1250059971834301^5231*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006127538572269047 25000000000000000000 1250059971834301 1250000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250059971834301/1250000000000000 : ℝ)) (X := (25006127538572269047/25000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(756692891035997/100000000000000000000 : ℝ) ≤ ((18016434418426597739/18017500000000000000 : ℝ)+2*(9002988189/28828000000000 : ℝ)*(9943/100000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (18016434418426597739/18017500000000000000 : ℝ)+2*(9002988189/28828000000000 : ℝ)*(9943/100000 : ℝ)=(5000014812632479/5000000000000000 : ℝ) by norm_num, show 1+2*(756692891035997/100000000000000000000 : ℝ)=(50000756692891035997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6127538572269047/50000000000000000000 : ℝ)+(756692891035997/100000000000000000000 : ℝ) ≤ ((18016434418426597739/18017500000000000000 : ℝ)+(9002988189/28828000000000 : ℝ)*((343/2000 : ℝ)+(9943/100000 : ℝ)))^(5231/1024 : ℝ) := by
    rw [show (18016434418426597739/18017500000000000000 : ℝ)+(9002988189/28828000000000 : ℝ)*((343/2000 : ℝ)+(9943/100000 : ℝ))=(10000254699969683/10000000000000000 : ℝ) by norm_num, show 1+(6127538572269047/50000000000000000000 : ℝ)+(756692891035997/100000000000000000000 : ℝ)=(100013011770035574091/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6127538572269047/50000000000000000000 : ℝ) ≤ ((18016434418426597739/18017500000000000000 : ℝ)+2*(9002988189/28828000000000 : ℝ)*(343/2000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (18016434418426597739/18017500000000000000 : ℝ)+2*(9002988189/28828000000000 : ℝ)*(343/2000 : ℝ)=(1250059971834301/1250000000000000 : ℝ) by norm_num, show 1+2*(6127538572269047/50000000000000000000 : ℝ)=(25006127538572269047/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18016434418426597739/18017500000000000000 : ℝ)*(X 1 0+X 2 0)+(9002988189/28828000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (9943/100000 : ℝ)) (hi := (343/2000 : ℝ)) (c := (18016434418426597739/18017500000000000000 : ℝ)) (alpha := (9002988189/28828000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18016434418426597739/18017500000000000000 : ℝ)*(X 0 1+X 2 1)+(9002988189/28828000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (9943/100000 : ℝ)) (hi := (343/2000 : ℝ)) (c := (18016434418426597739/18017500000000000000 : ℝ)) (alpha := (9002988189/28828000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18016434418426597739/18017500000000000000 : ℝ)*(X 0 2+X 1 2)+(9002988189/28828000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (9943/100000 : ℝ)) (hi := (343/2000 : ℝ)) (c := (18016434418426597739/18017500000000000000 : ℝ)) (alpha := (9002988189/28828000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-720758629/5000000000 : ℝ)*X 0 0+(5475178363/10000000000 : ℝ)*X 0 1+(1027448909/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673098571/5000000000 : ℝ)*X 1 0+(-404215141/2500000000 : ℝ)*X 1 1+(2568622813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133654899/250000000 : ℝ)*X 2 0+(2568623347/5000000000 : ℝ)*X 2 1+(-161686073/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((823022789/2000000000 : ℝ)*X 0 0+(3652337663/10000000000 : ℝ)*X 0 1+(1153553767/2500000000 : ℝ)*X 0 2+(823022789/2000000000 : ℝ)*X 1 0+(3652337663/10000000000 : ℝ)*X 1 1+(1153553767/2500000000 : ℝ)*X 1 2+(823022789/2000000000 : ℝ)*X 2 0+(3652337663/10000000000 : ℝ)*X 2 1+(1153553767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-360418003/2500000000 : ℝ)*X 0 0+(1285240501/2500000000 : ℝ)*X 0 1+(5471405457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627884537/5000000000 : ℝ)*X 1 0+(-641351283/5000000000 : ℝ)*X 1 1+(5471405197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255769059/10000000000 : ℝ)*X 2 0+(341962829/625000000 : ℝ)*X 2 1+(-1282702493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4115557729/10000000000 : ℝ)*X 0 0+(4603636879/10000000000 : ℝ)*X 0 1+(146522809/400000000 : ℝ)*X 0 2+(4115557729/10000000000 : ℝ)*X 1 0+(4603636879/10000000000 : ℝ)*X 1 1+(146522809/400000000 : ℝ)*X 1 2+(4115557729/10000000000 : ℝ)*X 2 0+(4603636879/10000000000 : ℝ)*X 2 1+(146522809/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2658911060819060721349629597/900875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1287367957/100000000000000 : ℝ)*(base19) + (30158291/5000000000000 : ℝ)*(base23) + (77572731/50000000000000 : ℝ)*(upper2) + (171153621/100000000000000 : ℝ)*(upper4) + (192844093/100000000000000 : ℝ)*(lower5) + (1999432188658141/100000000000000 : ℝ)*(major0) + (1999432188658141/100000000000000 : ℝ)*(major1) + (1999432188658141/100000000000000 : ℝ)*(major2) + (1479596095976553/50000000000000 : ℝ)*(sp0) + (739804802880273/25000000000000 : ℝ)*(sp1) + (739804973930807/25000000000000 : ℝ)*(sp2) + (519819211303697/50000000000000 : ℝ)*(sp3) + (14153467971/50000000000000 : ℝ)*(sp4) + (2678718649/50000000000000 : ℝ)*(sp7) + (259910945011173/25000000000000 : ℝ)*(f.failure) + (369902562361131/12500000000000 : ℝ)*(f.sum) + (1219668325839/1441400000000000000000000000 : ℝ)*base66 + (13643247231417331801/1801750000000000000000000000000000 : ℝ)*base68 + (2114787145435331801/1801750000000000000000000000000000 : ℝ)*base70 + (11196863920112831801/1801750000000000000000000000000000 : ℝ)*base72 + (35070844544887/7207000000000000000000000000 : ℝ)*base74 + (1522583361840668199/1801750000000000000000000000000000 : ℝ)*base75 + (6311670708590831801/1801750000000000000000000000000000 : ℝ)*base78 + (1462237417557168199/1801750000000000000000000000000000 : ℝ)*base79 + (5427380609969/7207000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1853683/312500000000000000000 : ℝ)*base89 + (1853683/312500000000000000000 : ℝ)*base91 + (1853683/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1043121261531476349589228347/450437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247938353/50000000000000 : ℝ)*(base19) + (255541413/50000000000000 : ℝ)*(base23) + (112914939/100000000000000 : ℝ)*(lower1) + (1174599/4000000000000 : ℝ)*(upper3) + (13505671/100000000000000 : ℝ)*(lower4) + (98238899/100000000000000 : ℝ)*(upper5) + (2044710714858109/100000000000000 : ℝ)*(major0) + (2044710714858109/100000000000000 : ℝ)*(major1) + (2044710714858109/100000000000000 : ℝ)*(major2) + (26936733/25000000000000 : ℝ)*(sp1) + (3026234119291759/100000000000000 : ℝ)*(sp4) + (75655837891703/2500000000000 : ℝ)*(sp5) + (3026233608208933/100000000000000 : ℝ)*(sp6) + (531593616615629/50000000000000 : ℝ)*(sp7) + (531593616615629/50000000000000 : ℝ)*(f.failure) + (3026234119291759/100000000000000 : ℝ)*(f.sum) + (13746676552387/7207000000000000000000000000 : ℝ)*base65 + (11569149198799340551/1801750000000000000000000000000000 : ℝ)*base67 + (6139230130116909449/1801750000000000000000000000000000 : ℝ)*base70 + (20818084206795340551/1801750000000000000000000000000000 : ℝ)*base71 + (25281953984707/7207000000000000000000000000 : ℝ)*base73 + (14293677525817340551/1801750000000000000000000000000000 : ℝ)*base75 + (4588974549455090551/1801750000000000000000000000000000 : ℝ)*base77 + (5769859580016340551/1801750000000000000000000000000000 : ℝ)*base79 + (17635431335881/3603500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3506141/625000000000000000000 : ℝ)*base90 + (3506141/625000000000000000000 : ℝ)*base92 + (3506141/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1702_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1243/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17149/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1702_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1702_box_0 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1116569749/10000000000 : ℝ)*x 0 + (5421497889/10000000000 : ℝ)*x 1 + (5421497939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1116569749/10000000000 : ℝ)^5239 ≤ (6555071952179/100000000000000 : ℝ)^4215 := by
    have hnat : (1116569749 : ℕ)^5239*100000000000000^4215 ≤ 6555071952179^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116569749 10000000000 6555071952179 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421497889/10000000000 : ℝ)^5239 ≤ (2336123187343/5000000000000 : ℝ)^4215 := by
    have hnat : (5421497889 : ℕ)^5239*5000000000000^4215 ≤ 2336123187343^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421497889 10000000000 2336123187343 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421497939/10000000000 : ℝ)^5239 ≤ (11680616070611/25000000000000 : ℝ)^4215 := by
    have hnat : (5421497939 : ℕ)^5239*25000000000000^4215 ≤ 11680616070611^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421497939 10000000000 11680616070611 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1116569749/10000000000 : ℝ), (5421497889/10000000000 : ℝ), (5421497939/10000000000 : ℝ)] ![(6555071952179/100000000000000 : ℝ), (2336123187343/5000000000000 : ℝ), (11680616070611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1116569749/10000000000 : ℝ)|^5239 ≤ (6555071952179/100000000000000 : ℝ)^4215
        have hw : |(-1116569749/10000000000 : ℝ)|=(1116569749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421497889/10000000000 : ℝ)|^5239 ≤ (2336123187343/5000000000000 : ℝ)^4215
        have hw : |(5421497889/10000000000 : ℝ)|=(5421497889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421497939/10000000000 : ℝ)|^5239 ≤ (11680616070611/25000000000000 : ℝ)^4215
        have hw : |(5421497939/10000000000 : ℝ)|=(5421497939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_1 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612869607/5000000000 : ℝ)*x 0 + (-697362497/5000000000 : ℝ)*x 1 + (1355374493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612869607/5000000000 : ℝ)^5239 ≤ (44634843337323/100000000000000 : ℝ)^4215 := by
    have hnat : (2612869607 : ℕ)^5239*100000000000000^4215 ≤ 44634843337323^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612869607 5000000000 44634843337323 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697362497/5000000000 : ℝ)^5239 ≤ (1728538401843/20000000000000 : ℝ)^4215 := by
    have hnat : (697362497 : ℕ)^5239*20000000000000^4215 ≤ 1728538401843^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697362497 5000000000 1728538401843 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355374493/2500000000 : ℝ)^5239 ≤ (46722464635929/100000000000000 : ℝ)^4215 := by
    have hnat : (1355374493 : ℕ)^5239*100000000000000^4215 ≤ 46722464635929^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355374493 2500000000 46722464635929 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612869607/5000000000 : ℝ), (-697362497/5000000000 : ℝ), (1355374493/2500000000 : ℝ)] ![(44634843337323/100000000000000 : ℝ), (1728538401843/20000000000000 : ℝ), (46722464635929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612869607/5000000000 : ℝ)|^5239 ≤ (44634843337323/100000000000000 : ℝ)^4215
        have hw : |(2612869607/5000000000 : ℝ)|=(2612869607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-697362497/5000000000 : ℝ)|^5239 ≤ (1728538401843/20000000000000 : ℝ)^4215
        have hw : |(-697362497/5000000000 : ℝ)|=(697362497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355374493/2500000000 : ℝ)|^5239 ≤ (46722464635929/100000000000000 : ℝ)^4215
        have hw : |(1355374493/2500000000 : ℝ)|=(1355374493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_2 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306434819/2500000000 : ℝ)*x 0 + (1355374483/2500000000 : ℝ)*x 1 + (-348681241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306434819/2500000000 : ℝ)^5239 ≤ (2231742199777/5000000000000 : ℝ)^4215 := by
    have hnat : (1306434819 : ℕ)^5239*5000000000000^4215 ≤ 2231742199777^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306434819 2500000000 2231742199777 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355374483/2500000000 : ℝ)^5239 ≤ (23361232103731/50000000000000 : ℝ)^4215 := by
    have hnat : (1355374483 : ℕ)^5239*50000000000000^4215 ≤ 23361232103731^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355374483 2500000000 23361232103731 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348681241/2500000000 : ℝ)^5239 ≤ (172853835563/2000000000000 : ℝ)^4215 := by
    have hnat : (348681241 : ℕ)^5239*2000000000000^4215 ≤ 172853835563^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348681241 2500000000 172853835563 2000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306434819/2500000000 : ℝ), (1355374483/2500000000 : ℝ), (-348681241/2500000000 : ℝ)] ![(2231742199777/5000000000000 : ℝ), (23361232103731/50000000000000 : ℝ), (172853835563/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306434819/2500000000 : ℝ)|^5239 ≤ (2231742199777/5000000000000 : ℝ)^4215
        have hw : |(1306434819/2500000000 : ℝ)|=(1306434819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355374483/2500000000 : ℝ)|^5239 ≤ (23361232103731/50000000000000 : ℝ)^4215
        have hw : |(1355374483/2500000000 : ℝ)|=(1355374483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-348681241/2500000000 : ℝ)|^5239 ≤ (172853835563/2000000000000 : ℝ)^4215
        have hw : |(-348681241/2500000000 : ℝ)|=(348681241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_3 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4497876447/10000000000 : ℝ)*x 0 + (986437693/2500000000 : ℝ)*x 1 + (246609429/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497876447/10000000000 : ℝ)^5239 ≤ (18521600940309/50000000000000 : ℝ)^4215 := by
    have hnat : (4497876447 : ℕ)^5239*50000000000000^4215 ≤ 18521600940309^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497876447 10000000000 18521600940309 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986437693/2500000000 : ℝ)^5239 ≤ (7869599650341/25000000000000 : ℝ)^4215 := by
    have hnat : (986437693 : ℕ)^5239*25000000000000^4215 ≤ 7869599650341^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986437693 2500000000 7869599650341 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246609429/625000000 : ℝ)^5239 ≤ (31478399513631/100000000000000 : ℝ)^4215 := by
    have hnat : (246609429 : ℕ)^5239*100000000000000^4215 ≤ 31478399513631^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246609429 625000000 31478399513631 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497876447/10000000000 : ℝ), (986437693/2500000000 : ℝ), (246609429/625000000 : ℝ)] ![(18521600940309/50000000000000 : ℝ), (7869599650341/25000000000000 : ℝ), (31478399513631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497876447/10000000000 : ℝ)|^5239 ≤ (18521600940309/50000000000000 : ℝ)^4215
        have hw : |(4497876447/10000000000 : ℝ)|=(4497876447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(986437693/2500000000 : ℝ)|^5239 ≤ (7869599650341/25000000000000 : ℝ)^4215
        have hw : |(986437693/2500000000 : ℝ)|=(986437693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(246609429/625000000 : ℝ)|^5239 ≤ (31478399513631/100000000000000 : ℝ)^4215
        have hw : |(246609429/625000000 : ℝ)|=(246609429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_4 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-893612523/5000000000 : ℝ)*x 0 + (1294267033/2500000000 : ℝ)*x 1 + (5177067483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893612523/5000000000 : ℝ)^5239 ≤ (2352514240763/20000000000000 : ℝ)^4215 := by
    have hnat : (893612523 : ℕ)^5239*20000000000000^4215 ≤ 2352514240763^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893612523 5000000000 2352514240763 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294267033/2500000000 : ℝ)^5239 ≤ (2205935891311/5000000000000 : ℝ)^4215 := by
    have hnat : (1294267033 : ℕ)^5239*5000000000000^4215 ≤ 2205935891311^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294267033 2500000000 2205935891311 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177067483/10000000000 : ℝ)^5239 ≤ (2757419434489/6250000000000 : ℝ)^4215 := by
    have hnat : (5177067483 : ℕ)^5239*6250000000000^4215 ≤ 2757419434489^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177067483 10000000000 2757419434489 6250000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-893612523/5000000000 : ℝ), (1294267033/2500000000 : ℝ), (5177067483/10000000000 : ℝ)] ![(2352514240763/20000000000000 : ℝ), (2205935891311/5000000000000 : ℝ), (2757419434489/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-893612523/5000000000 : ℝ)|^5239 ≤ (2352514240763/20000000000000 : ℝ)^4215
        have hw : |(-893612523/5000000000 : ℝ)|=(893612523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294267033/2500000000 : ℝ)|^5239 ≤ (2205935891311/5000000000000 : ℝ)^4215
        have hw : |(1294267033/2500000000 : ℝ)|=(1294267033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177067483/10000000000 : ℝ)|^5239 ≤ (2757419434489/6250000000000 : ℝ)^4215
        have hw : |(5177067483/10000000000 : ℝ)|=(5177067483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_5 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168494597/312500000 : ℝ)*x 0 + (-750995311/5000000000 : ℝ)*x 1 + (20708269/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168494597/312500000 : ℝ)^5239 ≤ (928097032199/2000000000000 : ℝ)^4215 := by
    have hnat : (168494597 : ℕ)^5239*2000000000000^4215 ≤ 928097032199^4215*312500000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168494597 312500000 928097032199 2000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750995311/5000000000 : ℝ)^5239 ≤ (18952879799/200000000000 : ℝ)^4215 := by
    have hnat : (750995311 : ℕ)^5239*200000000000^4215 ≤ 18952879799^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750995311 5000000000 18952879799 200000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20708269/40000000 : ℝ)^5239 ≤ (44118708483821/100000000000000 : ℝ)^4215 := by
    have hnat : (20708269 : ℕ)^5239*100000000000000^4215 ≤ 44118708483821^4215*40000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20708269 40000000 44118708483821 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168494597/312500000 : ℝ), (-750995311/5000000000 : ℝ), (20708269/40000000 : ℝ)] ![(928097032199/2000000000000 : ℝ), (18952879799/200000000000 : ℝ), (44118708483821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168494597/312500000 : ℝ)|^5239 ≤ (928097032199/2000000000000 : ℝ)^4215
        have hw : |(168494597/312500000 : ℝ)|=(168494597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-750995311/5000000000 : ℝ)|^5239 ≤ (18952879799/200000000000 : ℝ)^4215
        have hw : |(-750995311/5000000000 : ℝ)|=(750995311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20708269/40000000 : ℝ)|^5239 ≤ (44118708483821/100000000000000 : ℝ)^4215
        have hw : |(20708269/40000000 : ℝ)|=(20708269/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_6 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168494627/312500000 : ℝ)*x 0 + (1294266641/2500000000 : ℝ)*x 1 + (-1501990239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168494627/312500000 : ℝ)^5239 ≤ (9280972375891/20000000000000 : ℝ)^4215 := by
    have hnat : (168494627 : ℕ)^5239*20000000000000^4215 ≤ 9280972375891^4215*312500000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168494627 312500000 9280972375891 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294266641/2500000000 : ℝ)^5239 ≤ (44118701217511/100000000000000 : ℝ)^4215 := by
    have hnat : (1294266641 : ℕ)^5239*100000000000000^4215 ≤ 44118701217511^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294266641 2500000000 44118701217511 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1501990239/10000000000 : ℝ)^5239 ≤ (296138653/3125000000 : ℝ)^4215 := by
    have hnat : (1501990239 : ℕ)^5239*3125000000^4215 ≤ 296138653^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501990239 10000000000 296138653 3125000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168494627/312500000 : ℝ), (1294266641/2500000000 : ℝ), (-1501990239/10000000000 : ℝ)] ![(9280972375891/20000000000000 : ℝ), (44118701217511/100000000000000 : ℝ), (296138653/3125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168494627/312500000 : ℝ)|^5239 ≤ (9280972375891/20000000000000 : ℝ)^4215
        have hw : |(168494627/312500000 : ℝ)|=(168494627/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294266641/2500000000 : ℝ)|^5239 ≤ (44118701217511/100000000000000 : ℝ)^4215
        have hw : |(1294266641/2500000000 : ℝ)|=(1294266641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1501990239/10000000000 : ℝ)|^5239 ≤ (296138653/3125000000 : ℝ)^4215
        have hw : |(-1501990239/10000000000 : ℝ)|=(1501990239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_7 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3717129527/10000000000 : ℝ)*x 0 + (1083820961/2500000000 : ℝ)*x 1 + (2167642193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3717129527/10000000000 : ℝ)^5239 ≤ (29227599428487/100000000000000 : ℝ)^4215 := by
    have hnat : (3717129527 : ℕ)^5239*100000000000000^4215 ≤ 29227599428487^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717129527 10000000000 29227599428487 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083820961/2500000000 : ℝ)^5239 ≤ (17693098766063/50000000000000 : ℝ)^4215 := by
    have hnat : (1083820961 : ℕ)^5239*50000000000000^4215 ≤ 17693098766063^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083820961 2500000000 17693098766063 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167642193/5000000000 : ℝ)^5239 ≤ (8846550757727/25000000000000 : ℝ)^4215 := by
    have hnat : (2167642193 : ℕ)^5239*25000000000000^4215 ≤ 8846550757727^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167642193 5000000000 8846550757727 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3717129527/10000000000 : ℝ), (1083820961/2500000000 : ℝ), (2167642193/5000000000 : ℝ)] ![(29227599428487/100000000000000 : ℝ), (17693098766063/50000000000000 : ℝ), (8846550757727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3717129527/10000000000 : ℝ)|^5239 ≤ (29227599428487/100000000000000 : ℝ)^4215
        have hw : |(3717129527/10000000000 : ℝ)|=(3717129527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083820961/2500000000 : ℝ)|^5239 ≤ (17693098766063/50000000000000 : ℝ)^4215
        have hw : |(1083820961/2500000000 : ℝ)|=(1083820961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2167642193/5000000000 : ℝ)|^5239 ≤ (8846550757727/25000000000000 : ℝ)^4215
        have hw : |(2167642193/5000000000 : ℝ)|=(2167642193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_8 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1643106653/10000000000 : ℝ)*x 0 + (4997072307/10000000000 : ℝ)*x 1 + (273228617/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643106653/10000000000 : ℝ)^5239 ≤ (2648854668617/25000000000000 : ℝ)^4215 := by
    have hnat : (1643106653 : ℕ)^5239*25000000000000^4215 ≤ 2648854668617^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643106653 10000000000 2648854668617 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997072307/10000000000 : ℝ)^5239 ≤ (5277534220597/12500000000000 : ℝ)^4215 := by
    have hnat : (4997072307 : ℕ)^5239*12500000000000^4215 ≤ 5277534220597^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997072307 10000000000 5277534220597 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273228617/500000000 : ℝ)^5239 ≤ (47184307541149/100000000000000 : ℝ)^4215 := by
    have hnat : (273228617 : ℕ)^5239*100000000000000^4215 ≤ 47184307541149^4215*500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273228617 500000000 47184307541149 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1643106653/10000000000 : ℝ), (4997072307/10000000000 : ℝ), (273228617/500000000 : ℝ)] ![(2648854668617/25000000000000 : ℝ), (5277534220597/12500000000000 : ℝ), (47184307541149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1643106653/10000000000 : ℝ)|^5239 ≤ (2648854668617/25000000000000 : ℝ)^4215
        have hw : |(-1643106653/10000000000 : ℝ)|=(1643106653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997072307/10000000000 : ℝ)|^5239 ≤ (5277534220597/12500000000000 : ℝ)^4215
        have hw : |(4997072307/10000000000 : ℝ)|=(4997072307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273228617/500000000 : ℝ)|^5239 ≤ (47184307541149/100000000000000 : ℝ)^4215
        have hw : |(273228617/500000000 : ℝ)|=(273228617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_9 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299121707/2500000000 : ℝ)*x 0 + (-137502119/1000000000 : ℝ)*x 1 + (2732286197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299121707/2500000000 : ℝ)^5239 ≤ (44324499894701/100000000000000 : ℝ)^4215 := by
    have hnat : (1299121707 : ℕ)^5239*100000000000000^4215 ≤ 44324499894701^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299121707 2500000000 44324499894701 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137502119/1000000000 : ℝ)^5239 ≤ (8491191966551/100000000000000 : ℝ)^4215 := by
    have hnat : (137502119 : ℕ)^5239*100000000000000^4215 ≤ 8491191966551^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137502119 1000000000 8491191966551 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732286197/5000000000 : ℝ)^5239 ≤ (11796077030173/25000000000000 : ℝ)^4215 := by
    have hnat : (2732286197 : ℕ)^5239*25000000000000^4215 ≤ 11796077030173^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732286197 5000000000 11796077030173 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299121707/2500000000 : ℝ), (-137502119/1000000000 : ℝ), (2732286197/5000000000 : ℝ)] ![(44324499894701/100000000000000 : ℝ), (8491191966551/100000000000000 : ℝ), (11796077030173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299121707/2500000000 : ℝ)|^5239 ≤ (44324499894701/100000000000000 : ℝ)^4215
        have hw : |(1299121707/2500000000 : ℝ)|=(1299121707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137502119/1000000000 : ℝ)|^5239 ≤ (8491191966551/100000000000000 : ℝ)^4215
        have hw : |(-137502119/1000000000 : ℝ)|=(137502119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732286197/5000000000 : ℝ)|^5239 ≤ (11796077030173/25000000000000 : ℝ)^4215
        have hw : |(2732286197/5000000000 : ℝ)|=(2732286197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_10 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598243437/5000000000 : ℝ)*x 0 + (5464572407/10000000000 : ℝ)*x 1 + (-1375021109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598243437/5000000000 : ℝ)^5239 ≤ (44324500382389/100000000000000 : ℝ)^4215 := by
    have hnat : (2598243437 : ℕ)^5239*100000000000000^4215 ≤ 44324500382389^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598243437 5000000000 44324500382389 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464572407/10000000000 : ℝ)^5239 ≤ (11796077065053/25000000000000 : ℝ)^4215 := by
    have hnat : (5464572407 : ℕ)^5239*25000000000000^4215 ≤ 11796077065053^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464572407 10000000000 11796077065053 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375021109/10000000000 : ℝ)^5239 ≤ (8491191344831/100000000000000 : ℝ)^4215 := by
    have hnat : (1375021109 : ℕ)^5239*100000000000000^4215 ≤ 8491191344831^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375021109 10000000000 8491191344831 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598243437/5000000000 : ℝ), (5464572407/10000000000 : ℝ), (-1375021109/10000000000 : ℝ)] ![(44324500382389/100000000000000 : ℝ), (11796077065053/25000000000000 : ℝ), (8491191344831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598243437/5000000000 : ℝ)|^5239 ≤ (44324500382389/100000000000000 : ℝ)^4215
        have hw : |(2598243437/5000000000 : ℝ)|=(2598243437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464572407/10000000000 : ℝ)|^5239 ≤ (11796077065053/25000000000000 : ℝ)^4215
        have hw : |(5464572407/10000000000 : ℝ)|=(5464572407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1375021109/10000000000 : ℝ)|^5239 ≤ (8491191344831/100000000000000 : ℝ)^4215
        have hw : |(-1375021109/10000000000 : ℝ)|=(1375021109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_11 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2315230577/5000000000 : ℝ)*x 0 + (1938462773/5000000000 : ℝ)*x 1 + (775385131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2315230577/5000000000 : ℝ)^5239 ≤ (38405230196799/100000000000000 : ℝ)^4215 := by
    have hnat : (2315230577 : ℕ)^5239*100000000000000^4215 ≤ 38405230196799^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315230577 5000000000 38405230196799 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938462773/5000000000 : ℝ)^5239 ≤ (30797384358079/100000000000000 : ℝ)^4215 := by
    have hnat : (1938462773 : ℕ)^5239*100000000000000^4215 ≤ 30797384358079^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938462773 5000000000 30797384358079 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775385131/2000000000 : ℝ)^5239 ≤ (15398692717153/50000000000000 : ℝ)^4215 := by
    have hnat : (775385131 : ℕ)^5239*50000000000000^4215 ≤ 15398692717153^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775385131 2000000000 15398692717153 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2315230577/5000000000 : ℝ), (1938462773/5000000000 : ℝ), (775385131/2000000000 : ℝ)] ![(38405230196799/100000000000000 : ℝ), (30797384358079/100000000000000 : ℝ), (15398692717153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2315230577/5000000000 : ℝ)|^5239 ≤ (38405230196799/100000000000000 : ℝ)^4215
        have hw : |(2315230577/5000000000 : ℝ)|=(2315230577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1938462773/5000000000 : ℝ)|^5239 ≤ (30797384358079/100000000000000 : ℝ)^4215
        have hw : |(1938462773/5000000000 : ℝ)|=(1938462773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(775385131/2000000000 : ℝ)|^5239 ≤ (15398692717153/50000000000000 : ℝ)^4215
        have hw : |(775385131/2000000000 : ℝ)|=(775385131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_12 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1255475797/10000000000 : ℝ)*x 0 + (2796408133/5000000000 : ℝ)*x 1 + (643983111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1255475797/10000000000 : ℝ)^5239 ≤ (3791762781471/50000000000000 : ℝ)^4215 := by
    have hnat : (1255475797 : ℕ)^5239*50000000000000^4215 ≤ 3791762781471^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255475797 10000000000 3791762781471 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796408133/5000000000 : ℝ)^5239 ≤ (4856455857161/10000000000000 : ℝ)^4215 := by
    have hnat : (2796408133 : ℕ)^5239*10000000000000^4215 ≤ 4856455857161^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796408133 5000000000 4856455857161 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643983111/1250000000 : ℝ)^5239 ≤ (43851915843349/100000000000000 : ℝ)^4215 := by
    have hnat : (643983111 : ℕ)^5239*100000000000000^4215 ≤ 43851915843349^4215*1250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643983111 1250000000 43851915843349 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1255475797/10000000000 : ℝ), (2796408133/5000000000 : ℝ), (643983111/1250000000 : ℝ)] ![(3791762781471/50000000000000 : ℝ), (4856455857161/10000000000000 : ℝ), (43851915843349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1255475797/10000000000 : ℝ)|^5239 ≤ (3791762781471/50000000000000 : ℝ)^4215
        have hw : |(-1255475797/10000000000 : ℝ)|=(1255475797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796408133/5000000000 : ℝ)|^5239 ≤ (4856455857161/10000000000000 : ℝ)^4215
        have hw : |(2796408133/5000000000 : ℝ)|=(2796408133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643983111/1250000000 : ℝ)|^5239 ≤ (43851915843349/100000000000000 : ℝ)^4215
        have hw : |(643983111/1250000000 : ℝ)|=(643983111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_13 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540898153/1000000000 : ℝ)*x 0 + (-1512592871/10000000000 : ℝ)*x 1 + (5151864853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540898153/1000000000 : ℝ)^5239 ≤ (9317686047157/20000000000000 : ℝ)^4215 := by
    have hnat : (540898153 : ℕ)^5239*20000000000000^4215 ≤ 9317686047157^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540898153 1000000000 9317686047157 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512592871/10000000000 : ℝ)^5239 ≤ (1911930855503/20000000000000 : ℝ)^4215 := by
    have hnat : (1512592871 : ℕ)^5239*20000000000000^4215 ≤ 1911930855503^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512592871 10000000000 1911930855503 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151864853/10000000000 : ℝ)^5239 ≤ (21925957736529/50000000000000 : ℝ)^4215 := by
    have hnat : (5151864853 : ℕ)^5239*50000000000000^4215 ≤ 21925957736529^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151864853 10000000000 21925957736529 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540898153/1000000000 : ℝ), (-1512592871/10000000000 : ℝ), (5151864853/10000000000 : ℝ)] ![(9317686047157/20000000000000 : ℝ), (1911930855503/20000000000000 : ℝ), (21925957736529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540898153/1000000000 : ℝ)|^5239 ≤ (9317686047157/20000000000000 : ℝ)^4215
        have hw : |(540898153/1000000000 : ℝ)|=(540898153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512592871/10000000000 : ℝ)|^5239 ≤ (1911930855503/20000000000000 : ℝ)^4215
        have hw : |(-1512592871/10000000000 : ℝ)|=(1512592871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151864853/10000000000 : ℝ)|^5239 ≤ (21925957736529/50000000000000 : ℝ)^4215
        have hw : |(5151864853/10000000000 : ℝ)|=(5151864853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_14 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408981639/10000000000 : ℝ)*x 0 + (515186473/1000000000 : ℝ)*x 1 + (-1512592889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408981639/10000000000 : ℝ)^5239 ≤ (23294215701351/50000000000000 : ℝ)^4215 := by
    have hnat : (5408981639 : ℕ)^5239*50000000000000^4215 ≤ 23294215701351^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408981639 10000000000 23294215701351 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515186473/1000000000 : ℝ)^5239 ≤ (43851914171751/100000000000000 : ℝ)^4215 := by
    have hnat : (515186473 : ℕ)^5239*100000000000000^4215 ≤ 43851914171751^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515186473 1000000000 43851914171751 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1512592889/10000000000 : ℝ)^5239 ≤ (9559654418913/100000000000000 : ℝ)^4215 := by
    have hnat : (1512592889 : ℕ)^5239*100000000000000^4215 ≤ 9559654418913^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512592889 10000000000 9559654418913 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408981639/10000000000 : ℝ), (515186473/1000000000 : ℝ), (-1512592889/10000000000 : ℝ)] ![(23294215701351/50000000000000 : ℝ), (43851914171751/100000000000000 : ℝ), (9559654418913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408981639/10000000000 : ℝ)|^5239 ≤ (23294215701351/50000000000000 : ℝ)^4215
        have hw : |(5408981639/10000000000 : ℝ)|=(5408981639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515186473/1000000000 : ℝ)|^5239 ≤ (43851914171751/100000000000000 : ℝ)^4215
        have hw : |(515186473/1000000000 : ℝ)|=(515186473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1512592889/10000000000 : ℝ)|^5239 ≤ (9559654418913/100000000000000 : ℝ)^4215
        have hw : |(-1512592889/10000000000 : ℝ)|=(1512592889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_box_15 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (90841087/250000000 : ℝ)*x 0 + (2187670463/5000000000 : ℝ)*x 1 + (273458777/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90841087/250000000 : ℝ)^5239 ≤ (3551739165323/12500000000000 : ℝ)^4215 := by
    have hnat : (90841087 : ℕ)^5239*12500000000000^4215 ≤ 3551739165323^4215*250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90841087 250000000 3551739165323 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187670463/5000000000 : ℝ)^5239 ≤ (35793045847527/100000000000000 : ℝ)^4215 := by
    have hnat : (2187670463 : ℕ)^5239*100000000000000^4215 ≤ 35793045847527^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187670463 5000000000 35793045847527 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273458777/625000000 : ℝ)^5239 ≤ (559266262883/1562500000000 : ℝ)^4215 := by
    have hnat : (273458777 : ℕ)^5239*1562500000000^4215 ≤ 559266262883^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273458777 625000000 559266262883 1562500000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90841087/250000000 : ℝ), (2187670463/5000000000 : ℝ), (273458777/625000000 : ℝ)] ![(3551739165323/12500000000000 : ℝ), (35793045847527/100000000000000 : ℝ), (559266262883/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90841087/250000000 : ℝ)|^5239 ≤ (3551739165323/12500000000000 : ℝ)^4215
        have hw : |(90841087/250000000 : ℝ)|=(90841087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2187670463/5000000000 : ℝ)|^5239 ≤ (35793045847527/100000000000000 : ℝ)^4215
        have hw : |(2187670463/5000000000 : ℝ)|=(2187670463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273458777/625000000 : ℝ)|^5239 ≤ (559266262883/1562500000000 : ℝ)^4215
        have hw : |(273458777/625000000 : ℝ)|=(273458777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1702_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1243/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(33337/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29107/50000 : ℝ) ∧ (40609/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22577/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17149/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1243/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17149/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1243/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17149/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1243/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17149/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1243/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17149/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1243/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17149/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1243/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1243/12500 : ℝ) ^ (5231/1024 : ℝ) ≤ (37854086810001/5000000000000000000 : ℝ) := by
    have hpowers : (1243/12500 : ℝ)^5231 ≤ (37854086810001/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1243 : ℕ)^5231*5000000000000000000^1024 ≤ 37854086810001^1024*12500^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1243 12500 37854086810001 5000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1243/12500 : ℝ)) (X := (37854086810001/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17149/100000 : ℝ) ^ (5231/1024 : ℝ) ≤ (12251427213412389/100000000000000000000 : ℝ) := by
    have hpowers : (17149/100000 : ℝ)^5231 ≤ (12251427213412389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17149 : ℕ)^5231*100000000000000000000^1024 ≤ 12251427213412389^1024*100000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17149 100000 12251427213412389 100000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17149/100000 : ℝ)) (X := (12251427213412389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500037854086810001/2500000000000000000 : ℝ) ≤ (10000029640488533/10000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (2500037854086810001/2500000000000000000 : ℝ)^1024 ≤ (10000029640488533/10000000000000000 : ℝ)^5231 := by
      have hnat : (2500037854086810001 : ℕ)^1024*10000000000000000^5231 ≤ 10000029640488533^5231*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500037854086810001 2500000000000000000 10000029640488533 10000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000029640488533/10000000000000000 : ℝ)) (X := (2500037854086810001/2500000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013008508949612409/100000000000000000000 : ℝ) ≤ (80002037089109/80000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (100013008508949612409/100000000000000000000 : ℝ)^1024 ≤ (80002037089109/80000000000000 : ℝ)^5231 := by
      have hnat : (100013008508949612409 : ℕ)^1024*80000000000000^5231 ≤ 80002037089109^5231*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013008508949612409 100000000000000000000 80002037089109 80000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002037089109/80000000000000 : ℝ)) (X := (100013008508949612409/100000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50012251427213412389/50000000000000000000 : ℝ) ≤ (10000479631788717/10000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (50012251427213412389/50000000000000000000 : ℝ)^1024 ≤ (10000479631788717/10000000000000000 : ℝ)^5231 := by
      have hnat : (50012251427213412389 : ℕ)^1024*10000000000000000^5231 ≤ 10000479631788717^5231*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012251427213412389 50000000000000000000 10000479631788717 10000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000479631788717/10000000000000000 : ℝ)) (X := (50012251427213412389/50000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(37854086810001/5000000000000000000 : ℝ) ≤ ((6549612622384622779/6550000000000000000 : ℝ)+2*(56248912523/180125000000000 : ℝ)*(1243/12500 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (6549612622384622779/6550000000000000000 : ℝ)+2*(56248912523/180125000000000 : ℝ)*(1243/12500 : ℝ)=(10000029640488533/10000000000000000 : ℝ) by norm_num, show 1+2*(37854086810001/5000000000000000000 : ℝ)=(2500037854086810001/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12251427213412389/100000000000000000000 : ℝ)+(37854086810001/5000000000000000000 : ℝ) ≤ ((6549612622384622779/6550000000000000000 : ℝ)+(56248912523/180125000000000 : ℝ)*((17149/100000 : ℝ)+(1243/12500 : ℝ)))^(5231/1024 : ℝ) := by
    rw [show (6549612622384622779/6550000000000000000 : ℝ)+(56248912523/180125000000000 : ℝ)*((17149/100000 : ℝ)+(1243/12500 : ℝ))=(80002037089109/80000000000000 : ℝ) by norm_num, show 1+(12251427213412389/100000000000000000000 : ℝ)+(37854086810001/5000000000000000000 : ℝ)=(100013008508949612409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12251427213412389/100000000000000000000 : ℝ) ≤ ((6549612622384622779/6550000000000000000 : ℝ)+2*(56248912523/180125000000000 : ℝ)*(17149/100000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (6549612622384622779/6550000000000000000 : ℝ)+2*(56248912523/180125000000000 : ℝ)*(17149/100000 : ℝ)=(10000479631788717/10000000000000000 : ℝ) by norm_num, show 1+2*(12251427213412389/100000000000000000000 : ℝ)=(50012251427213412389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6549612622384622779/6550000000000000000 : ℝ)*(X 1 0+X 2 0)+(56248912523/180125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1243/12500 : ℝ)) (hi := (17149/100000 : ℝ)) (c := (6549612622384622779/6550000000000000000 : ℝ)) (alpha := (56248912523/180125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6549612622384622779/6550000000000000000 : ℝ)*(X 0 1+X 2 1)+(56248912523/180125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1243/12500 : ℝ)) (hi := (17149/100000 : ℝ)) (c := (6549612622384622779/6550000000000000000 : ℝ)) (alpha := (56248912523/180125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6549612622384622779/6550000000000000000 : ℝ)*(X 0 2+X 1 2)+(56248912523/180125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1243/12500 : ℝ)) (hi := (17149/100000 : ℝ)) (c := (6549612622384622779/6550000000000000000 : ℝ)) (alpha := (56248912523/180125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1116569749/10000000000 : ℝ)*X 0 0+(5421497889/10000000000 : ℝ)*X 0 1+(5421497939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612869607/5000000000 : ℝ)*X 1 0+(-697362497/5000000000 : ℝ)*X 1 1+(1355374493/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1306434819/2500000000 : ℝ)*X 2 0+(1355374483/2500000000 : ℝ)*X 2 1+(-348681241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4497876447/10000000000 : ℝ)*X 0 0+(986437693/2500000000 : ℝ)*X 0 1+(246609429/625000000 : ℝ)*X 0 2+(4497876447/10000000000 : ℝ)*X 1 0+(986437693/2500000000 : ℝ)*X 1 1+(246609429/625000000 : ℝ)*X 1 2+(4497876447/10000000000 : ℝ)*X 2 0+(986437693/2500000000 : ℝ)*X 2 1+(246609429/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-893612523/5000000000 : ℝ)*X 0 0+(1294267033/2500000000 : ℝ)*X 0 1+(5177067483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((168494597/312500000 : ℝ)*X 1 0+(-750995311/5000000000 : ℝ)*X 1 1+(20708269/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((168494627/312500000 : ℝ)*X 2 0+(1294266641/2500000000 : ℝ)*X 2 1+(-1501990239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3717129527/10000000000 : ℝ)*X 0 0+(1083820961/2500000000 : ℝ)*X 0 1+(2167642193/5000000000 : ℝ)*X 0 2+(3717129527/10000000000 : ℝ)*X 1 0+(1083820961/2500000000 : ℝ)*X 1 1+(2167642193/5000000000 : ℝ)*X 1 2+(3717129527/10000000000 : ℝ)*X 2 0+(1083820961/2500000000 : ℝ)*X 2 1+(2167642193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1643106653/10000000000 : ℝ)*X 0 0+(4997072307/10000000000 : ℝ)*X 0 1+(273228617/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1299121707/2500000000 : ℝ)*X 1 0+(-137502119/1000000000 : ℝ)*X 1 1+(2732286197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598243437/5000000000 : ℝ)*X 2 0+(5464572407/10000000000 : ℝ)*X 2 1+(-1375021109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2315230577/5000000000 : ℝ)*X 0 0+(1938462773/5000000000 : ℝ)*X 0 1+(775385131/2000000000 : ℝ)*X 0 2+(2315230577/5000000000 : ℝ)*X 1 0+(1938462773/5000000000 : ℝ)*X 1 1+(775385131/2000000000 : ℝ)*X 1 2+(2315230577/5000000000 : ℝ)*X 2 0+(1938462773/5000000000 : ℝ)*X 2 1+(775385131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1255475797/10000000000 : ℝ)*X 0 0+(2796408133/5000000000 : ℝ)*X 0 1+(643983111/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((540898153/1000000000 : ℝ)*X 1 0+(-1512592871/10000000000 : ℝ)*X 1 1+(5151864853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5408981639/10000000000 : ℝ)*X 2 0+(515186473/1000000000 : ℝ)*X 2 1+(-1512592889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((90841087/250000000 : ℝ)*X 0 0+(2187670463/5000000000 : ℝ)*X 0 1+(273458777/625000000 : ℝ)*X 0 2+(90841087/250000000 : ℝ)*X 1 0+(2187670463/5000000000 : ℝ)*X 1 1+(273458777/625000000 : ℝ)*X 1 2+(90841087/250000000 : ℝ)*X 2 0+(2187670463/5000000000 : ℝ)*X 2 1+(273458777/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33337/50000 : ℝ) ≤ (-600459930979900578526092561845307/900625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107163831/100000000000000 : ℝ)*(upper0) + (79328199/50000000000000 : ℝ)*(lower2) + (2863301/10000000000000 : ℝ)*(lower3) + (668161337895199/50000000000000 : ℝ)*(major0) + (668161337895199/50000000000000 : ℝ)*(major1) + (668161337895199/50000000000000 : ℝ)*(major2) + (4242296433/100000000000000 : ℝ)*(sp1) + (781247289/12500000000000 : ℝ)*(sp2) + (233269417/50000000000000 : ℝ)*(sp3) + (2000019143278863/100000000000000 : ℝ)*(sp4) + (2000017882749543/100000000000000 : ℝ)*(sp5) + (125000992191729/6250000000000 : ℝ)*(sp6) + (694846583488181/100000000000000 : ℝ)*(sp7) + (372720889/12500000000000 : ℝ)*(sp8) + (138969410005403/20000000000000 : ℝ)*(f.failure) + (250002765630747/12500000000000 : ℝ)*(f.sum) + (117165831828159/36025000000000000000000000000 : ℝ)*base66 + (3606579277302318231/3602500000000000000000000000000000 : ℝ)*base67 + (7659516951695181769/3602500000000000000000000000000000 : ℝ)*base70 + (32208075816415181769/3602500000000000000000000000000000 : ℝ)*base72 + (6375435463313/1125781250000000000000000000 : ℝ)*base73 + (18303847899687681769/3602500000000000000000000000000000 : ℝ)*base76 + (33970661891500181769/3602500000000000000000000000000000 : ℝ)*base78 + (7776513690647681769/3602500000000000000000000000000000 : ℝ)*base80 + (13229559670417/18012500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2423013/250000000000000000000 : ℝ)*base89 + (2423013/250000000000000000000 : ℝ)*base91 + (2423013/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29107/50000 : ℝ) ≤ (1048632915700328596560028057750269/1801250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3746507/50000000000000 : ℝ)*(lower1) + (404767/5000000000000 : ℝ)*(lower3) + (9404897/100000000000000 : ℝ)*(upper4) + (719408673663767/50000000000000 : ℝ)*(major0) + (719408673663767/50000000000000 : ℝ)*(major1) + (719408673663767/50000000000000 : ℝ)*(major2) + (1055043865697853/50000000000000 : ℝ)*(sp0) + (211008740569463/10000000000000 : ℝ)*(sp1) + (527521906780959/25000000000000 : ℝ)*(sp2) + (374070544114619/50000000000000 : ℝ)*(sp3) + (241318973/50000000000000 : ℝ)*(sp5) + (13060437/5000000000000 : ℝ)*(sp6) + (66171889/100000000000000 : ℝ)*(sp7) + (15693687/10000000000000 : ℝ)*(sp12) + (748141154401127/100000000000000 : ℝ)*(f.failure) + (65940246510393/3125000000000 : ℝ)*(f.sum) + (153613661085503/36025000000000000000000000000 : ℝ)*base65 + (8412244434781966577/3602500000000000000000000000000000 : ℝ)*base68 + (42654843341616966577/3602500000000000000000000000000000 : ℝ)*base70 + (6178572292050533423/3602500000000000000000000000000000 : ℝ)*base71 + (2666455725657/9006250000000000000000000000 : ℝ)*base73 + (8565183319868033423/3602500000000000000000000000000000 : ℝ)*base75 + (8350861001379466577/3602500000000000000000000000000000 : ℝ)*base78 + (7283525194726966577/3602500000000000000000000000000000 : ℝ)*base80 + (947782079020289/18012500000000000000000000000 : ℝ)*base81 + (334617/1250000000000000000000 : ℝ)*base89 + (334617/1250000000000000000000 : ℝ)*base91 + (334617/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40609/50000 : ℝ) ≤ (292595572731751562631516426577443/360250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21363817/100000000000000 : ℝ)*(upper0) + (16577/100000000000000 : ℝ)*(upper1) + (22029/500000000000 : ℝ)*(upper3) + (45451/200000000000 : ℝ)*(upper4) + (146355799925517/10000000000000 : ℝ)*(major0) + (146355799925517/10000000000000 : ℝ)*(major1) + (146355799925517/10000000000000 : ℝ)*(major2) + (207825703/12500000000000 : ℝ)*(sp1) + (6067688821/100000000000000 : ℝ)*(sp2) + (90164819/25000000000000 : ℝ)*(sp3) + (427807415538239/20000000000000 : ℝ)*(sp8) + (2139035415085571/100000000000000 : ℝ)*(sp9) + (1069515505001187/50000000000000 : ℝ)*(sp10) + (380502589229517/50000000000000 : ℝ)*(sp11) + (76100553911831/10000000000000 : ℝ)*(f.failure) + (427807415538239/20000000000000 : ℝ)*(f.sum) + (2150074943163/7205000000000000000000000000 : ℝ)*base65 + (2012366456542969173/720500000000000000000000000000000 : ℝ)*base67 + (1054823734016469173/720500000000000000000000000000000 : ℝ)*base69 + (167846518507469173/720500000000000000000000000000000 : ℝ)*base71 + (8807378776161/3602500000000000000000000000 : ℝ)*base74 + (3989005800975469173/720500000000000000000000000000000 : ℝ)*base75 + (2547244344873469173/720500000000000000000000000000000 : ℝ)*base77 + (1289218240780469173/720500000000000000000000000000000 : ℝ)*base79 + (3600770866177/1801250000000000000000000000 : ℝ)*base81 + (113801/125000000000000000000 : ℝ)*base89 + (113801/125000000000000000000 : ℝ)*base91 + (113801/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-22577/25000 : ℝ) ≤ (-1626631518476344945569839413949727/1801250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9480119/25000000000000 : ℝ)*(upper1) + (300909/4000000000000 : ℝ)*(lower2) + (864247/3125000000000 : ℝ)*(upper3) + (266301/800000000000 : ℝ)*(upper5) + (1511942980640861/100000000000000 : ℝ)*(major0) + (1511942980640861/100000000000000 : ℝ)*(major1) + (1511942980640861/100000000000000 : ℝ)*(major2) + (923392439/100000000000000 : ℝ)*(sp4) + (2506263573/25000000000000 : ℝ)*(sp6) + (6054747843/100000000000000 : ℝ)*(sp7) + (2267822685395689/100000000000000 : ℝ)*(sp12) + (70869487774629/3125000000000 : ℝ)*(sp13) + (566953395933459/25000000000000 : ℝ)*(sp14) + (98269774943123/12500000000000 : ℝ)*(sp15) + (786164254292827/100000000000000 : ℝ)*(f.failure) + (70869487774629/3125000000000 : ℝ)*(f.sum) + (52226052995569/18012500000000000000000000000 : ℝ)*base66 + (21236859525577699909/7205000000000000000000000000000000 : ℝ)*base67 + (48661204502892699909/7205000000000000000000000000000000 : ℝ)*base69 + (36233739032362699909/7205000000000000000000000000000000 : ℝ)*base71 + (5859087792609/1125781250000000000000000000 : ℝ)*base74 + (9167828146682300091/7205000000000000000000000000000000 : ℝ)*base76 + (16917047197702699909/7205000000000000000000000000000000 : ℝ)*base77 + (25330987325647699909/7205000000000000000000000000000000 : ℝ)*base79 + (58242700643569/18012500000000000000000000000 : ℝ)*base82 + (5194683/1250000000000000000000 : ℝ)*base90 + (5194683/1250000000000000000000 : ℝ)*base92 + (5194683/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1702_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1243/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33337/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29107/50000 : ℝ) else (40609/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22577/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1702_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1702_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33337/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29107/50000 : ℝ) else (40609/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22577/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1702_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1702_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1702_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33337/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29107/50000 : ℝ) else (40609/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22577/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1702_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

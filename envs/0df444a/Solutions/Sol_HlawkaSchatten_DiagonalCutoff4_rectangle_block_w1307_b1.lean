-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:36.202287+00:00
-- url     : https://prove2.me/submissions/47f8ac90-f835-4673-9e22-33fa9bc48a07

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
theorem support_rectangle_w1307_s3_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036220599/5000000000 : ℝ)*x 0 + (5431892813/10000000000 : ℝ)*x 1 + (5227502647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036220599/5000000000 : ℝ)^4267 ≤ (12608304305317/100000000000000 : ℝ)^3243 := by
    have hnat : (1036220599 : ℕ)^4267*100000000000000^3243 ≤ 12608304305317^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036220599 5000000000 12608304305317 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431892813/10000000000 : ℝ)^4267 ≤ (559976992637/1250000000000 : ℝ)^3243 := by
    have hnat : (5431892813 : ℕ)^4267*1250000000000^3243 ≤ 559976992637^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431892813 10000000000 559976992637 1250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227502647/10000000000 : ℝ)^4267 ≤ (8518707253303/20000000000000 : ℝ)^3243 := by
    have hnat : (5227502647 : ℕ)^4267*20000000000000^3243 ≤ 8518707253303^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227502647 10000000000 8518707253303 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036220599/5000000000 : ℝ), (5431892813/10000000000 : ℝ), (5227502647/10000000000 : ℝ)] ![(12608304305317/100000000000000 : ℝ), (559976992637/1250000000000 : ℝ), (8518707253303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036220599/5000000000 : ℝ)|^4267 ≤ (12608304305317/100000000000000 : ℝ)^3243
        have hw : |(-1036220599/5000000000 : ℝ)|=(1036220599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431892813/10000000000 : ℝ)|^4267 ≤ (559976992637/1250000000000 : ℝ)^3243
        have hw : |(5431892813/10000000000 : ℝ)|=(5431892813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227502647/10000000000 : ℝ)|^4267 ≤ (8518707253303/20000000000000 : ℝ)^3243
        have hw : |(5227502647/10000000000 : ℝ)|=(5227502647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353978657/10000000000 : ℝ)*x 0 + (-2176998999/10000000000 : ℝ)*x 1 + (5227502597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353978657/10000000000 : ℝ)^4267 ≤ (8790920965879/20000000000000 : ℝ)^3243 := by
    have hnat : (5353978657 : ℕ)^4267*20000000000000^3243 ≤ 8790920965879^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353978657 10000000000 8790920965879 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176998999/10000000000 : ℝ)^4267 ≤ (1681482428433/12500000000000 : ℝ)^3243 := by
    have hnat : (2176998999 : ℕ)^4267*12500000000000^3243 ≤ 1681482428433^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176998999 10000000000 1681482428433 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227502597/10000000000 : ℝ)^4267 ≤ (42593535730477/100000000000000 : ℝ)^3243 := by
    have hnat : (5227502597 : ℕ)^4267*100000000000000^3243 ≤ 42593535730477^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227502597 10000000000 42593535730477 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353978657/10000000000 : ℝ), (-2176998999/10000000000 : ℝ), (5227502597/10000000000 : ℝ)] ![(8790920965879/20000000000000 : ℝ), (1681482428433/12500000000000 : ℝ), (42593535730477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353978657/10000000000 : ℝ)|^4267 ≤ (8790920965879/20000000000000 : ℝ)^3243
        have hw : |(5353978657/10000000000 : ℝ)|=(5353978657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176998999/10000000000 : ℝ)|^4267 ≤ (1681482428433/12500000000000 : ℝ)^3243
        have hw : |(-2176998999/10000000000 : ℝ)|=(2176998999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227502597/10000000000 : ℝ)|^4267 ≤ (42593535730477/100000000000000 : ℝ)^3243
        have hw : |(5227502597/10000000000 : ℝ)|=(5227502597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214159143/400000000 : ℝ)*x 0 + (522750279/1000000000 : ℝ)*x 1 + (-1088499427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214159143/400000000 : ℝ)^4267 ≤ (2747162746477/6250000000000 : ℝ)^3243 := by
    have hnat : (214159143 : ℕ)^4267*6250000000000^3243 ≤ 2747162746477^3243*400000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214159143 400000000 2747162746477 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522750279/1000000000 : ℝ)^4267 ≤ (21296768899791/50000000000000 : ℝ)^3243 := by
    have hnat : (522750279 : ℕ)^4267*50000000000000^3243 ≤ 21296768899791^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522750279 1000000000 21296768899791 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088499427/5000000000 : ℝ)^4267 ≤ (13451858248589/100000000000000 : ℝ)^3243 := by
    have hnat : (1088499427 : ℕ)^4267*100000000000000^3243 ≤ 13451858248589^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088499427 5000000000 13451858248589 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214159143/400000000 : ℝ), (522750279/1000000000 : ℝ), (-1088499427/5000000000 : ℝ)] ![(2747162746477/6250000000000 : ℝ), (21296768899791/50000000000000 : ℝ), (13451858248589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214159143/400000000 : ℝ)|^4267 ≤ (2747162746477/6250000000000 : ℝ)^3243
        have hw : |(214159143/400000000 : ℝ)|=(214159143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522750279/1000000000 : ℝ)|^4267 ≤ (21296768899791/50000000000000 : ℝ)^3243
        have hw : |(522750279/1000000000 : ℝ)|=(522750279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088499427/5000000000 : ℝ)|^4267 ≤ (13451858248589/100000000000000 : ℝ)^3243
        have hw : |(-1088499427/5000000000 : ℝ)|=(1088499427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334553821/10000000000 : ℝ)*x 0 + (1032049569/2500000000 : ℝ)*x 1 + (2275338623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334553821/10000000000 : ℝ)^4267 ≤ (33289482753617/100000000000000 : ℝ)^3243 := by
    have hnat : (4334553821 : ℕ)^4267*100000000000000^3243 ≤ 33289482753617^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334553821 10000000000 33289482753617 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032049569/2500000000 : ℝ)^4267 ≤ (31220096832109/100000000000000 : ℝ)^3243 := by
    have hnat : (1032049569 : ℕ)^4267*100000000000000^3243 ≤ 31220096832109^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032049569 2500000000 31220096832109 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275338623/5000000000 : ℝ)^4267 ≤ (35490420400391/100000000000000 : ℝ)^3243 := by
    have hnat : (2275338623 : ℕ)^4267*100000000000000^3243 ≤ 35490420400391^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275338623 5000000000 35490420400391 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334553821/10000000000 : ℝ), (1032049569/2500000000 : ℝ), (2275338623/5000000000 : ℝ)] ![(33289482753617/100000000000000 : ℝ), (31220096832109/100000000000000 : ℝ), (35490420400391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334553821/10000000000 : ℝ)|^4267 ≤ (33289482753617/100000000000000 : ℝ)^3243
        have hw : |(4334553821/10000000000 : ℝ)|=(4334553821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032049569/2500000000 : ℝ)|^4267 ≤ (31220096832109/100000000000000 : ℝ)^3243
        have hw : |(1032049569/2500000000 : ℝ)|=(1032049569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2275338623/5000000000 : ℝ)|^4267 ≤ (35490420400391/100000000000000 : ℝ)^3243
        have hw : |(2275338623/5000000000 : ℝ)|=(2275338623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-518115667/2500000000 : ℝ)*x 0 + (1045674723/2000000000 : ℝ)*x 1 + (2715508223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518115667/2500000000 : ℝ)^4267 ≤ (504339046741/4000000000000 : ℝ)^3243 := by
    have hnat : (518115667 : ℕ)^4267*4000000000000^3243 ≤ 504339046741^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518115667 2500000000 504339046741 4000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045674723/2000000000 : ℝ)^4267 ≤ (21301436970749/50000000000000 : ℝ)^3243 := by
    have hnat : (1045674723 : ℕ)^4267*50000000000000^3243 ≤ 21301436970749^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045674723 2000000000 21301436970749 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715508223/5000000000 : ℝ)^4267 ≤ (44788649868401/100000000000000 : ℝ)^3243 := by
    have hnat : (2715508223 : ℕ)^4267*100000000000000^3243 ≤ 44788649868401^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715508223 5000000000 44788649868401 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-518115667/2500000000 : ℝ), (1045674723/2000000000 : ℝ), (2715508223/5000000000 : ℝ)] ![(504339046741/4000000000000 : ℝ), (21301436970749/50000000000000 : ℝ), (44788649868401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-518115667/2500000000 : ℝ)|^4267 ≤ (504339046741/4000000000000 : ℝ)^3243
        have hw : |(-518115667/2500000000 : ℝ)|=(518115667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045674723/2000000000 : ℝ)|^4267 ≤ (21301436970749/50000000000000 : ℝ)^3243
        have hw : |(1045674723/2000000000 : ℝ)|=(1045674723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715508223/5000000000 : ℝ)|^4267 ≤ (44788649868401/100000000000000 : ℝ)^3243
        have hw : |(2715508223/5000000000 : ℝ)|=(2715508223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212061937/400000000 : ℝ)*x 0 + (-246685631/1250000000 : ℝ)*x 1 + (5431016411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212061937/400000000 : ℝ)^4267 ≤ (21694566000141/50000000000000 : ℝ)^3243 := by
    have hnat : (212061937 : ℕ)^4267*50000000000000^3243 ≤ 21694566000141^3243*400000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212061937 400000000 21694566000141 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246685631/1250000000 : ℝ)^4267 ≤ (94577747919/800000000000 : ℝ)^3243 := by
    have hnat : (246685631 : ℕ)^4267*800000000000^3243 ≤ 94577747919^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246685631 1250000000 94577747919 800000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431016411/10000000000 : ℝ)^4267 ≤ (22394324744311/50000000000000 : ℝ)^3243 := by
    have hnat : (5431016411 : ℕ)^4267*50000000000000^3243 ≤ 22394324744311^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431016411 10000000000 22394324744311 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212061937/400000000 : ℝ), (-246685631/1250000000 : ℝ), (5431016411/10000000000 : ℝ)] ![(21694566000141/50000000000000 : ℝ), (94577747919/800000000000 : ℝ), (22394324744311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212061937/400000000 : ℝ)|^4267 ≤ (21694566000141/50000000000000 : ℝ)^3243
        have hw : |(212061937/400000000 : ℝ)|=(212061937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246685631/1250000000 : ℝ)|^4267 ≤ (94577747919/800000000000 : ℝ)^3243
        have hw : |(-246685631/1250000000 : ℝ)|=(246685631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431016411/10000000000 : ℝ)|^4267 ≤ (22394324744311/50000000000000 : ℝ)^3243
        have hw : |(5431016411/10000000000 : ℝ)|=(5431016411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10354587/19531250 : ℝ)*x 0 + (5431016293/10000000000 : ℝ)*x 1 + (-1973485049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10354587/19531250 : ℝ)^4267 ≤ (4338913328173/10000000000000 : ℝ)^3243 := by
    have hnat : (10354587 : ℕ)^4267*10000000000000^3243 ≤ 4338913328173^3243*19531250^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10354587 19531250 4338913328173 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431016293/10000000000 : ℝ)^4267 ≤ (1791545928329/4000000000000 : ℝ)^3243 := by
    have hnat : (5431016293 : ℕ)^4267*4000000000000^3243 ≤ 1791545928329^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431016293 10000000000 1791545928329 4000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973485049/10000000000 : ℝ)^4267 ≤ (11822218497757/100000000000000 : ℝ)^3243 := by
    have hnat : (1973485049 : ℕ)^4267*100000000000000^3243 ≤ 11822218497757^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973485049 10000000000 11822218497757 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10354587/19531250 : ℝ), (5431016293/10000000000 : ℝ), (-1973485049/10000000000 : ℝ)] ![(4338913328173/10000000000000 : ℝ), (1791545928329/4000000000000 : ℝ), (11822218497757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10354587/19531250 : ℝ)|^4267 ≤ (4338913328173/10000000000000 : ℝ)^3243
        have hw : |(10354587/19531250 : ℝ)|=(10354587/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431016293/10000000000 : ℝ)|^4267 ≤ (1791545928329/4000000000000 : ℝ)^3243
        have hw : |(5431016293/10000000000 : ℝ)|=(5431016293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973485049/10000000000 : ℝ)|^4267 ≤ (11822218497757/100000000000000 : ℝ)^3243
        have hw : |(-1973485049/10000000000 : ℝ)|=(1973485049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s3_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135456199/312500000 : ℝ)*x 0 + (90977537/200000000 : ℝ)*x 1 + (4130009443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135456199/312500000 : ℝ)^4267 ≤ (832248322597/2500000000000 : ℝ)^3243 := by
    have hnat : (135456199 : ℕ)^4267*2500000000000^3243 ≤ 832248322597^3243*312500000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135456199 312500000 832248322597 2500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90977537/200000000 : ℝ)^4267 ≤ (35471946792867/100000000000000 : ℝ)^3243 := by
    have hnat : (90977537 : ℕ)^4267*100000000000000^3243 ≤ 35471946792867^3243*200000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90977537 200000000 35471946792867 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130009443/10000000000 : ℝ)^4267 ≤ (1249524811351/4000000000000 : ℝ)^3243 := by
    have hnat : (4130009443 : ℕ)^4267*4000000000000^3243 ≤ 1249524811351^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130009443 10000000000 1249524811351 4000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135456199/312500000 : ℝ), (90977537/200000000 : ℝ), (4130009443/10000000000 : ℝ)] ![(832248322597/2500000000000 : ℝ), (35471946792867/100000000000000 : ℝ), (1249524811351/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135456199/312500000 : ℝ)|^4267 ≤ (832248322597/2500000000000 : ℝ)^3243
        have hw : |(135456199/312500000 : ℝ)|=(135456199/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90977537/200000000 : ℝ)|^4267 ≤ (35471946792867/100000000000000 : ℝ)^3243
        have hw : |(90977537/200000000 : ℝ)|=(90977537/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130009443/10000000000 : ℝ)|^4267 ≤ (1249524811351/4000000000000 : ℝ)^3243
        have hw : |(4130009443/10000000000 : ℝ)|=(4130009443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10723/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13/80 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13/80 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13/80 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13/80 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13/80 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13/80 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9613/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (1447153067509887/25000000000000000000 : ℝ) := by
    have hpowers : (9613/100000 : ℝ)^2133 ≤ (1447153067509887/25000000000000000000 : ℝ)^512 := by
      have hnat : (9613 : ℕ)^2133*25000000000000000000^512 ≤ 1447153067509887^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9613 100000 1447153067509887 25000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9613/100000 : ℝ)) (X := (1447153067509887/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13/80 : ℝ) ^ (2133/512 : ℝ) ≤ (51570671869077391/100000000000000000000 : ℝ) := by
    have hpowers : (13/80 : ℝ)^2133 ≤ (51570671869077391/100000000000000000000 : ℝ)^512 := by
      have hnat : (13 : ℕ)^2133*100000000000000000000^512 ≤ 51570671869077391^512*80^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 80 51570671869077391 100000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/80 : ℝ)) (X := (51570671869077391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501447153067509887/12500000000000000000 : ℝ) ≤ (2500069471146533/2500000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (12501447153067509887/12500000000000000000 : ℝ)^512 ≤ (2500069471146533/2500000000000000 : ℝ)^2133 := by
      have hnat : (12501447153067509887 : ℕ)^512*2500000000000000^2133 ≤ 2500069471146533^2133*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501447153067509887 12500000000000000000 2500069471146533 2500000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069471146533/2500000000000000 : ℝ)) (X := (12501447153067509887/12500000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057359284139116939/100000000000000000000 : ℝ) ≤ (200027530759263/200000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (100057359284139116939/100000000000000000000 : ℝ)^512 ≤ (200027530759263/200000000000000 : ℝ)^2133 := by
      have hnat : (100057359284139116939 : ℕ)^512*200000000000000^2133 ≤ 200027530759263^2133*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057359284139116939 100000000000000000000 200027530759263 200000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200027530759263/200000000000000 : ℝ)) (X := (100057359284139116939/100000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50051570671869077391/50000000000000000000 : ℝ) ≤ (1250309398917521/1250000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (50051570671869077391/50000000000000000000 : ℝ)^512 ≤ (1250309398917521/1250000000000000 : ℝ)^2133 := by
      have hnat : (50051570671869077391 : ℕ)^512*1250000000000000^2133 ≤ 1250309398917521^2133*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50051570671869077391 50000000000000000000 1250309398917521 1250000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250309398917521/1250000000000000 : ℝ)) (X := (50051570671869077391/50000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1447153067509887/25000000000000000000 : ℝ) ≤ ((2073460050317862813/2074062500000000000 : ℝ)+2*(549326688509/331850000000000 : ℝ)*(9613/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (2073460050317862813/2074062500000000000 : ℝ)+2*(549326688509/331850000000000 : ℝ)*(9613/100000 : ℝ)=(2500069471146533/2500000000000000 : ℝ) by norm_num, show 1+2*(1447153067509887/25000000000000000000 : ℝ)=(12501447153067509887/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51570671869077391/100000000000000000000 : ℝ)+(1447153067509887/25000000000000000000 : ℝ) ≤ ((2073460050317862813/2074062500000000000 : ℝ)+(549326688509/331850000000000 : ℝ)*((13/80 : ℝ)+(9613/100000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (2073460050317862813/2074062500000000000 : ℝ)+(549326688509/331850000000000 : ℝ)*((13/80 : ℝ)+(9613/100000 : ℝ))=(200027530759263/200000000000000 : ℝ) by norm_num, show 1+(51570671869077391/100000000000000000000 : ℝ)+(1447153067509887/25000000000000000000 : ℝ)=(100057359284139116939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51570671869077391/100000000000000000000 : ℝ) ≤ ((2073460050317862813/2074062500000000000 : ℝ)+2*(549326688509/331850000000000 : ℝ)*(13/80 : ℝ))^(2133/512 : ℝ) := by
    rw [show (2073460050317862813/2074062500000000000 : ℝ)+2*(549326688509/331850000000000 : ℝ)*(13/80 : ℝ)=(1250309398917521/1250000000000000 : ℝ) by norm_num, show 1+2*(51570671869077391/100000000000000000000 : ℝ)=(50051570671869077391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2073460050317862813/2074062500000000000 : ℝ)*(X 1 0+X 2 0)+(549326688509/331850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (9613/100000 : ℝ)) (hi := (13/80 : ℝ)) (c := (2073460050317862813/2074062500000000000 : ℝ)) (alpha := (549326688509/331850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2073460050317862813/2074062500000000000 : ℝ)*(X 0 1+X 2 1)+(549326688509/331850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (9613/100000 : ℝ)) (hi := (13/80 : ℝ)) (c := (2073460050317862813/2074062500000000000 : ℝ)) (alpha := (549326688509/331850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2073460050317862813/2074062500000000000 : ℝ)*(X 0 2+X 1 2)+(549326688509/331850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (9613/100000 : ℝ)) (hi := (13/80 : ℝ)) (c := (2073460050317862813/2074062500000000000 : ℝ)) (alpha := (549326688509/331850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1036220599/5000000000 : ℝ)*X 0 0+(5431892813/10000000000 : ℝ)*X 0 1+(5227502647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353978657/10000000000 : ℝ)*X 1 0+(-2176998999/10000000000 : ℝ)*X 1 1+(5227502597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214159143/400000000 : ℝ)*X 2 0+(522750279/1000000000 : ℝ)*X 2 1+(-1088499427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4334553821/10000000000 : ℝ)*X 0 0+(1032049569/2500000000 : ℝ)*X 0 1+(2275338623/5000000000 : ℝ)*X 0 2+(4334553821/10000000000 : ℝ)*X 1 0+(1032049569/2500000000 : ℝ)*X 1 1+(2275338623/5000000000 : ℝ)*X 1 2+(4334553821/10000000000 : ℝ)*X 2 0+(1032049569/2500000000 : ℝ)*X 2 1+(2275338623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-518115667/2500000000 : ℝ)*X 0 0+(1045674723/2000000000 : ℝ)*X 0 1+(2715508223/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212061937/400000000 : ℝ)*X 1 0+(-246685631/1250000000 : ℝ)*X 1 1+(5431016411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10354587/19531250 : ℝ)*X 2 0+(5431016293/10000000000 : ℝ)*X 2 1+(-1973485049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((135456199/312500000 : ℝ)*X 0 0+(90977537/200000000 : ℝ)*X 0 1+(4130009443/10000000000 : ℝ)*X 0 2+(135456199/312500000 : ℝ)*X 1 0+(90977537/200000000 : ℝ)*X 1 1+(4130009443/10000000000 : ℝ)*X 1 2+(135456199/312500000 : ℝ)*X 2 0+(90977537/200000000 : ℝ)*X 2 1+(4130009443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77178613604742549678924483/10370312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (249210997/20000000000000 : ℝ)*(base19) + (1161099593/100000000000000 : ℝ)*(base23) + (4443489/6250000000000 : ℝ)*(upper3) + (5365227/100000000000000 : ℝ)*(upper4) + (24887517/12500000000000 : ℝ)*(upper5) + (90745637639369/2500000000000 : ℝ)*(major0) + (90745637639369/2500000000000 : ℝ)*(major1) + (90745637639369/2500000000000 : ℝ)*(major2) + (2446311992895347/50000000000000 : ℝ)*(sp0) + (489264726487129/10000000000000 : ℝ)*(sp1) + (2446323674913341/50000000000000 : ℝ)*(sp2) + (2366992841139111/100000000000000 : ℝ)*(sp3) + (24525135581/100000000000000 : ℝ)*(sp4) + (470550431/5000000000000 : ℝ)*(sp7) + (236700225214773/10000000000000 : ℝ)*(f.failure) + (1223162127731569/25000000000000 : ℝ)*(f.sum) + (4624105094991/6637000000000000000000000000 : ℝ)*base66 + (30192022318811863/20740625000000000000000000000000 : ℝ)*base67 + (122348874040860619/10370312500000000000000000000000 : ℝ)*base69 + (151695049363261863/20740625000000000000000000000000 : ℝ)*base71 + (20328378716363/3318500000000000000000000000 : ℝ)*base74 + (54527025299272497/5185156250000000000000000000000 : ℝ)*base75 + (91976969754074363/20740625000000000000000000000000 : ℝ)*base77 + (31853605722053747/5185156250000000000000000000000 : ℝ)*base79 + (2764352367443/663700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2613557/250000000000000000000 : ℝ)*base90 + (2613557/250000000000000000000 : ℝ)*base92 + (2613557/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80658255921630228766010787/20740625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223241293/20000000000000 : ℝ)*(base19) + (250146013/20000000000000 : ℝ)*(base23) + (110259347/100000000000000 : ℝ)*(upper3) + (972029/10000000000000 : ℝ)*(lower4) + (117470393/100000000000000 : ℝ)*(upper5) + (732218230515679/20000000000000 : ℝ)*(major0) + (732218230515679/20000000000000 : ℝ)*(major1) + (732218230515679/20000000000000 : ℝ)*(major2) + (1174557199/6250000000000 : ℝ)*(sp1) + (19341154407/100000000000000 : ℝ)*(sp2) + (2467395827459241/50000000000000 : ℝ)*(sp4) + (2467385872898417/50000000000000 : ℝ)*(sp5) + (493477106303401/10000000000000 : ℝ)*(sp6) + (29842381507603/1250000000000 : ℝ)*(sp7) + (29842381507603/1250000000000 : ℝ)*(f.failure) + (2467395827459241/50000000000000 : ℝ)*(f.sum) + (7222277865953/3318500000000000000000000000 : ℝ)*base66 + (250512396334426277/41481250000000000000000000000000 : ℝ)*base67 + (70638297647411223/41481250000000000000000000000000 : ℝ)*base70 + (281956286185798723/41481250000000000000000000000000 : ℝ)*base72 + (14986840435699/3318500000000000000000000000 : ℝ)*base73 + (184928294235223723/41481250000000000000000000000000 : ℝ)*base76 + (81722025135167473/41481250000000000000000000000000 : ℝ)*base78 + (17944631260011223/41481250000000000000000000000000 : ℝ)*base80 + (488782217651/3318500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (287473/31250000000000000000 : ℝ)*base89 + (287473/31250000000000000000 : ℝ)*base91 + (287473/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1307_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1307_s4_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037105853/5000000000 : ℝ)*x 0 + (677223757/1250000000 : ℝ)*x 1 + (5240444173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037105853/5000000000 : ℝ)^4267 ≤ (1262247876829/10000000000000 : ℝ)^3243 := by
    have hnat : (1037105853 : ℕ)^4267*10000000000000^3243 ≤ 1262247876829^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037105853 5000000000 1262247876829 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677223757/1250000000 : ℝ)^4267 ≤ (44645187906551/100000000000000 : ℝ)^3243 := by
    have hnat : (677223757 : ℕ)^4267*100000000000000^3243 ≤ 44645187906551^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677223757 1250000000 44645187906551 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240444173/10000000000 : ℝ)^4267 ≤ (21366166658457/50000000000000 : ℝ)^3243 := by
    have hnat : (5240444173 : ℕ)^4267*50000000000000^3243 ≤ 21366166658457^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240444173 10000000000 21366166658457 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037105853/5000000000 : ℝ), (677223757/1250000000 : ℝ), (5240444173/10000000000 : ℝ)] ![(1262247876829/10000000000000 : ℝ), (44645187906551/100000000000000 : ℝ), (21366166658457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037105853/5000000000 : ℝ)|^4267 ≤ (1262247876829/10000000000000 : ℝ)^3243
        have hw : |(-1037105853/5000000000 : ℝ)|=(1037105853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677223757/1250000000 : ℝ)|^4267 ≤ (44645187906551/100000000000000 : ℝ)^3243
        have hw : |(677223757/1250000000 : ℝ)|=(677223757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240444173/10000000000 : ℝ)|^4267 ≤ (21366166658457/50000000000000 : ℝ)^3243
        have hw : |(5240444173/10000000000 : ℝ)|=(5240444173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675202371/5000000000 : ℝ)*x 0 + (-2164663933/10000000000 : ℝ)*x 1 + (5240444183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675202371/5000000000 : ℝ)^4267 ≤ (43916003534007/100000000000000 : ℝ)^3243 := by
    have hnat : (2675202371 : ℕ)^4267*100000000000000^3243 ≤ 43916003534007^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675202371 5000000000 43916003534007 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164663933/10000000000 : ℝ)^4267 ≤ (3337915758733/25000000000000 : ℝ)^3243 := by
    have hnat : (2164663933 : ℕ)^4267*25000000000000^3243 ≤ 3337915758733^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164663933 10000000000 3337915758733 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240444183/10000000000 : ℝ)^4267 ≤ (8546466684841/20000000000000 : ℝ)^3243 := by
    have hnat : (5240444183 : ℕ)^4267*20000000000000^3243 ≤ 8546466684841^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240444183 10000000000 8546466684841 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675202371/5000000000 : ℝ), (-2164663933/10000000000 : ℝ), (5240444183/10000000000 : ℝ)] ![(43916003534007/100000000000000 : ℝ), (3337915758733/25000000000000 : ℝ), (8546466684841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675202371/5000000000 : ℝ)|^4267 ≤ (43916003534007/100000000000000 : ℝ)^3243
        have hw : |(2675202371/5000000000 : ℝ)|=(2675202371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2164663933/10000000000 : ℝ)|^4267 ≤ (3337915758733/25000000000000 : ℝ)^3243
        have hw : |(-2164663933/10000000000 : ℝ)|=(2164663933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240444183/10000000000 : ℝ)|^4267 ≤ (8546466684841/20000000000000 : ℝ)^3243
        have hw : |(5240444183/10000000000 : ℝ)|=(5240444183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675202371/5000000000 : ℝ)*x 0 + (1310111047/2500000000 : ℝ)*x 1 + (-1082331963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675202371/5000000000 : ℝ)^4267 ≤ (43916003534007/100000000000000 : ℝ)^3243 := by
    have hnat : (2675202371 : ℕ)^4267*100000000000000^3243 ≤ 43916003534007^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675202371 5000000000 43916003534007 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310111047/2500000000 : ℝ)^4267 ≤ (42732333477851/100000000000000 : ℝ)^3243 := by
    have hnat : (1310111047 : ℕ)^4267*100000000000000^3243 ≤ 42732333477851^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310111047 2500000000 42732333477851 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082331963/5000000000 : ℝ)^4267 ≤ (13351662978123/100000000000000 : ℝ)^3243 := by
    have hnat : (1082331963 : ℕ)^4267*100000000000000^3243 ≤ 13351662978123^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082331963 5000000000 13351662978123 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675202371/5000000000 : ℝ), (1310111047/2500000000 : ℝ), (-1082331963/5000000000 : ℝ)] ![(43916003534007/100000000000000 : ℝ), (42732333477851/100000000000000 : ℝ), (13351662978123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675202371/5000000000 : ℝ)|^4267 ≤ (43916003534007/100000000000000 : ℝ)^3243
        have hw : |(2675202371/5000000000 : ℝ)|=(2675202371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310111047/2500000000 : ℝ)|^4267 ≤ (42732333477851/100000000000000 : ℝ)^3243
        have hw : |(1310111047/2500000000 : ℝ)|=(1310111047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082331963/5000000000 : ℝ)|^4267 ≤ (13351662978123/100000000000000 : ℝ)^3243
        have hw : |(-1082331963/5000000000 : ℝ)|=(1082331963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335625569/10000000000 : ℝ)*x 0 + (4156014371/10000000000 : ℝ)*x 1 + (2261296201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335625569/10000000000 : ℝ)^4267 ≤ (16650156620183/50000000000000 : ℝ)^3243 := by
    have hnat : (4335625569 : ℕ)^4267*50000000000000^3243 ≤ 16650156620183^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335625569 10000000000 16650156620183 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4156014371/10000000000 : ℝ)^4267 ≤ (15748588869653/50000000000000 : ℝ)^3243 := by
    have hnat : (4156014371 : ℕ)^4267*50000000000000^3243 ≤ 15748588869653^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156014371 10000000000 15748588869653 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261296201/5000000000 : ℝ)^4267 ≤ (17601254501783/50000000000000 : ℝ)^3243 := by
    have hnat : (2261296201 : ℕ)^4267*50000000000000^3243 ≤ 17601254501783^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261296201 5000000000 17601254501783 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335625569/10000000000 : ℝ), (4156014371/10000000000 : ℝ), (2261296201/5000000000 : ℝ)] ![(16650156620183/50000000000000 : ℝ), (15748588869653/50000000000000 : ℝ), (17601254501783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335625569/10000000000 : ℝ)|^4267 ≤ (16650156620183/50000000000000 : ℝ)^3243
        have hw : |(4335625569/10000000000 : ℝ)|=(4335625569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4156014371/10000000000 : ℝ)|^4267 ≤ (15748588869653/50000000000000 : ℝ)^3243
        have hw : |(4156014371/10000000000 : ℝ)|=(4156014371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261296201/5000000000 : ℝ)|^4267 ≤ (17601254501783/50000000000000 : ℝ)^3243
        have hw : |(2261296201/5000000000 : ℝ)|=(2261296201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414845151/2000000000 : ℝ)*x 0 + (5241100563/10000000000 : ℝ)*x 1 + (2708565063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414845151/2000000000 : ℝ)^4267 ≤ (1577823907261/12500000000000 : ℝ)^3243 := by
    have hnat : (414845151 : ℕ)^4267*12500000000000^3243 ≤ 1577823907261^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414845151 2000000000 1577823907261 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241100563/10000000000 : ℝ)^4267 ≤ (21369687972437/50000000000000 : ℝ)^3243 := by
    have hnat : (5241100563 : ℕ)^4267*50000000000000^3243 ≤ 21369687972437^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241100563 10000000000 21369687972437 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708565063/5000000000 : ℝ)^4267 ≤ (44638032773779/100000000000000 : ℝ)^3243 := by
    have hnat : (2708565063 : ℕ)^4267*100000000000000^3243 ≤ 44638032773779^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708565063 5000000000 44638032773779 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414845151/2000000000 : ℝ), (5241100563/10000000000 : ℝ), (2708565063/5000000000 : ℝ)] ![(1577823907261/12500000000000 : ℝ), (21369687972437/50000000000000 : ℝ), (44638032773779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414845151/2000000000 : ℝ)|^4267 ≤ (1577823907261/12500000000000 : ℝ)^3243
        have hw : |(-414845151/2000000000 : ℝ)|=(414845151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241100563/10000000000 : ℝ)|^4267 ≤ (21369687972437/50000000000000 : ℝ)^3243
        have hw : |(5241100563/10000000000 : ℝ)|=(5241100563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708565063/5000000000 : ℝ)|^4267 ≤ (44638032773779/100000000000000 : ℝ)^3243
        have hw : |(2708565063/5000000000 : ℝ)|=(2708565063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304914463/10000000000 : ℝ)*x 0 + (-248497249/1250000000 : ℝ)*x 1 + (677141257/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304914463/10000000000 : ℝ)^4267 ≤ (339260802389/781250000000 : ℝ)^3243 := by
    have hnat : (5304914463 : ℕ)^4267*781250000000^3243 ≤ 339260802389^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304914463 10000000000 339260802389 781250000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248497249/1250000000 : ℝ)^4267 ≤ (746036578703/6250000000000 : ℝ)^3243 := by
    have hnat : (248497249 : ℕ)^4267*6250000000000^3243 ≤ 746036578703^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248497249 1250000000 746036578703 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677141257/1250000000 : ℝ)^4267 ≤ (8927606402967/20000000000000 : ℝ)^3243 := by
    have hnat : (677141257 : ℕ)^4267*20000000000000^3243 ≤ 8927606402967^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677141257 1250000000 8927606402967 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304914463/10000000000 : ℝ), (-248497249/1250000000 : ℝ), (677141257/1250000000 : ℝ)] ![(339260802389/781250000000 : ℝ), (746036578703/6250000000000 : ℝ), (8927606402967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304914463/10000000000 : ℝ)|^4267 ≤ (339260802389/781250000000 : ℝ)^3243
        have hw : |(5304914463/10000000000 : ℝ)|=(5304914463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248497249/1250000000 : ℝ)|^4267 ≤ (746036578703/6250000000000 : ℝ)^3243
        have hw : |(-248497249/1250000000 : ℝ)|=(248497249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677141257/1250000000 : ℝ)|^4267 ≤ (8927606402967/20000000000000 : ℝ)^3243
        have hw : |(677141257/1250000000 : ℝ)|=(677141257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530491433/1000000000 : ℝ)*x 0 + (5417130213/10000000000 : ℝ)*x 1 + (-1987977959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530491433/1000000000 : ℝ)^4267 ≤ (43425381273299/100000000000000 : ℝ)^3243 := by
    have hnat : (530491433 : ℕ)^4267*100000000000000^3243 ≤ 43425381273299^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530491433 1000000000 43425381273299 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417130213/10000000000 : ℝ)^4267 ≤ (44638033717037/100000000000000 : ℝ)^3243 := by
    have hnat : (5417130213 : ℕ)^4267*100000000000000^3243 ≤ 44638033717037^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417130213 10000000000 44638033717037 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987977959/10000000000 : ℝ)^4267 ≤ (5968292499269/50000000000000 : ℝ)^3243 := by
    have hnat : (1987977959 : ℕ)^4267*50000000000000^3243 ≤ 5968292499269^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987977959 10000000000 5968292499269 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530491433/1000000000 : ℝ), (5417130213/10000000000 : ℝ), (-1987977959/10000000000 : ℝ)] ![(43425381273299/100000000000000 : ℝ), (44638033717037/100000000000000 : ℝ), (5968292499269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530491433/1000000000 : ℝ)|^4267 ≤ (43425381273299/100000000000000 : ℝ)^3243
        have hw : |(530491433/1000000000 : ℝ)|=(530491433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417130213/10000000000 : ℝ)|^4267 ≤ (44638033717037/100000000000000 : ℝ)^3243
        have hw : |(5417130213/10000000000 : ℝ)|=(5417130213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987977959/10000000000 : ℝ)|^4267 ≤ (5968292499269/50000000000000 : ℝ)^3243
        have hw : |(-1987977959/10000000000 : ℝ)|=(1987977959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s4_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083913607/2500000000 : ℝ)*x 0 + (4521235651/10000000000 : ℝ)*x 1 + (4157378439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083913607/2500000000 : ℝ)^4267 ≤ (33300604884993/100000000000000 : ℝ)^3243 := by
    have hnat : (1083913607 : ℕ)^4267*100000000000000^3243 ≤ 33300604884993^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083913607 2500000000 33300604884993 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521235651/10000000000 : ℝ)^4267 ≤ (35188614550927/100000000000000 : ℝ)^3243 := by
    have hnat : (4521235651 : ℕ)^4267*100000000000000^3243 ≤ 35188614550927^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521235651 10000000000 35188614550927 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4157378439/10000000000 : ℝ)^4267 ≤ (393884756939/1250000000000 : ℝ)^3243 := by
    have hnat : (4157378439 : ℕ)^4267*1250000000000^3243 ≤ 393884756939^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157378439 10000000000 393884756939 1250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083913607/2500000000 : ℝ), (4521235651/10000000000 : ℝ), (4157378439/10000000000 : ℝ)] ![(33300604884993/100000000000000 : ℝ), (35188614550927/100000000000000 : ℝ), (393884756939/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083913607/2500000000 : ℝ)|^4267 ≤ (33300604884993/100000000000000 : ℝ)^3243
        have hw : |(1083913607/2500000000 : ℝ)|=(1083913607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521235651/10000000000 : ℝ)|^4267 ≤ (35188614550927/100000000000000 : ℝ)^3243
        have hw : |(4521235651/10000000000 : ℝ)|=(4521235651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4157378439/10000000000 : ℝ)|^4267 ≤ (393884756939/1250000000000 : ℝ)^3243
        have hw : |(4157378439/10000000000 : ℝ)|=(4157378439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10999/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10723/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10723/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10723/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10723/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10723/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10723/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10723/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (365041777740689/4000000000000000000 : ℝ) := by
    have hpowers : (10723/100000 : ℝ)^2133 ≤ (365041777740689/4000000000000000000 : ℝ)^512 := by
      have hnat : (10723 : ℕ)^2133*4000000000000000000^512 ≤ 365041777740689^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10723 100000 365041777740689 4000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10723/100000 : ℝ)) (X := (365041777740689/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15047/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (7486408381836943/20000000000000000000 : ℝ) := by
    have hpowers : (15047/100000 : ℝ)^2133 ≤ (7486408381836943/20000000000000000000 : ℝ)^512 := by
      have hnat : (15047 : ℕ)^2133*20000000000000000000^512 ≤ 7486408381836943^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15047 100000 7486408381836943 20000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15047/100000 : ℝ)) (X := (7486408381836943/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000365041777740689/2000000000000000000 : ℝ) ≤ (1000043808820707/1000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (2000365041777740689/2000000000000000000 : ℝ)^512 ≤ (1000043808820707/1000000000000000 : ℝ)^2133 := by
      have hnat : (2000365041777740689 : ℕ)^512*1000000000000000^2133 ≤ 1000043808820707^2133*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000365041777740689 2000000000000000000 1000043808820707 1000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000043808820707/1000000000000000 : ℝ)) (X := (2000365041777740689/2000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002327904317635097/5000000000000000000 : ℝ) ≤ (10001117371035249/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (5002327904317635097/5000000000000000000 : ℝ)^512 ≤ (10001117371035249/10000000000000000 : ℝ)^2133 := by
      have hnat : (5002327904317635097 : ℕ)^512*10000000000000000^2133 ≤ 10001117371035249^2133*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002327904317635097 5000000000000000000 10001117371035249 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001117371035249/10000000000000000 : ℝ)) (X := (5002327904317635097/5000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007486408381836943/10000000000000000000 : ℝ) ≤ (2500449163465857/2500000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (10007486408381836943/10000000000000000000 : ℝ)^512 ≤ (2500449163465857/2500000000000000 : ℝ)^2133 := by
      have hnat : (10007486408381836943 : ℕ)^512*2500000000000000^2133 ≤ 2500449163465857^2133*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007486408381836943 10000000000000000000 2500449163465857 2500000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500449163465857/2500000000000000 : ℝ)) (X := (10007486408381836943/10000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(365041777740689/4000000000000000000 : ℝ) ≤ ((21613663196937121923/21620000000000000000 : ℝ)+2*(679282828179/432400000000000 : ℝ)*(10723/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (21613663196937121923/21620000000000000000 : ℝ)+2*(679282828179/432400000000000 : ℝ)*(10723/100000 : ℝ)=(1000043808820707/1000000000000000 : ℝ) by norm_num, show 1+2*(365041777740689/4000000000000000000 : ℝ)=(2000365041777740689/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7486408381836943/20000000000000000000 : ℝ)+(365041777740689/4000000000000000000 : ℝ) ≤ ((21613663196937121923/21620000000000000000 : ℝ)+(679282828179/432400000000000 : ℝ)*((15047/100000 : ℝ)+(10723/100000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (21613663196937121923/21620000000000000000 : ℝ)+(679282828179/432400000000000 : ℝ)*((15047/100000 : ℝ)+(10723/100000 : ℝ))=(10001117371035249/10000000000000000 : ℝ) by norm_num, show 1+(7486408381836943/20000000000000000000 : ℝ)+(365041777740689/4000000000000000000 : ℝ)=(5002327904317635097/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7486408381836943/20000000000000000000 : ℝ) ≤ ((21613663196937121923/21620000000000000000 : ℝ)+2*(679282828179/432400000000000 : ℝ)*(15047/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (21613663196937121923/21620000000000000000 : ℝ)+2*(679282828179/432400000000000 : ℝ)*(15047/100000 : ℝ)=(2500449163465857/2500000000000000 : ℝ) by norm_num, show 1+2*(7486408381836943/20000000000000000000 : ℝ)=(10007486408381836943/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21613663196937121923/21620000000000000000 : ℝ)*(X 1 0+X 2 0)+(679282828179/432400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (15047/100000 : ℝ)) (c := (21613663196937121923/21620000000000000000 : ℝ)) (alpha := (679282828179/432400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21613663196937121923/21620000000000000000 : ℝ)*(X 0 1+X 2 1)+(679282828179/432400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (15047/100000 : ℝ)) (c := (21613663196937121923/21620000000000000000 : ℝ)) (alpha := (679282828179/432400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21613663196937121923/21620000000000000000 : ℝ)*(X 0 2+X 1 2)+(679282828179/432400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (15047/100000 : ℝ)) (c := (21613663196937121923/21620000000000000000 : ℝ)) (alpha := (679282828179/432400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1037105853/5000000000 : ℝ)*X 0 0+(677223757/1250000000 : ℝ)*X 0 1+(5240444173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675202371/5000000000 : ℝ)*X 1 0+(-2164663933/10000000000 : ℝ)*X 1 1+(5240444183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675202371/5000000000 : ℝ)*X 2 0+(1310111047/2500000000 : ℝ)*X 2 1+(-1082331963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335625569/10000000000 : ℝ)*X 0 0+(4156014371/10000000000 : ℝ)*X 0 1+(2261296201/5000000000 : ℝ)*X 0 2+(4335625569/10000000000 : ℝ)*X 1 0+(4156014371/10000000000 : ℝ)*X 1 1+(2261296201/5000000000 : ℝ)*X 1 2+(4335625569/10000000000 : ℝ)*X 2 0+(4156014371/10000000000 : ℝ)*X 2 1+(2261296201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-414845151/2000000000 : ℝ)*X 0 0+(5241100563/10000000000 : ℝ)*X 0 1+(2708565063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304914463/10000000000 : ℝ)*X 1 0+(-248497249/1250000000 : ℝ)*X 1 1+(677141257/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530491433/1000000000 : ℝ)*X 2 0+(5417130213/10000000000 : ℝ)*X 2 1+(-1987977959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083913607/2500000000 : ℝ)*X 0 0+(4521235651/10000000000 : ℝ)*X 0 1+(4157378439/10000000000 : ℝ)*X 0 2+(1083913607/2500000000 : ℝ)*X 1 0+(4521235651/10000000000 : ℝ)*X 1 1+(4157378439/10000000000 : ℝ)*X 1 2+(1083913607/2500000000 : ℝ)*X 2 0+(4521235651/10000000000 : ℝ)*X 2 1+(4157378439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65255594263707732303894507/5875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2117089443/100000000000000 : ℝ)*(base19) + (987872023/50000000000000 : ℝ)*(base23) + (18906377/25000000000000 : ℝ)*(lower2) + (280013949/100000000000000 : ℝ)*(upper3) + (182318991/100000000000000 : ℝ)*(upper5) + (522922288154177/12500000000000 : ℝ)*(major0) + (522922288154177/12500000000000 : ℝ)*(major1) + (522922288154177/12500000000000 : ℝ)*(major2) + (5638741767774887/100000000000000 : ℝ)*(sp0) + (1127756230348383/20000000000000 : ℝ)*(sp1) + (352423830817957/6250000000000 : ℝ)*(sp2) + (1363975758577889/50000000000000 : ℝ)*(sp3) + (41501056471/100000000000000 : ℝ)*(sp4) + (2681779397/12500000000000 : ℝ)*(sp7) + (1363986485695477/50000000000000 : ℝ)*(f.failure) + (5638783268831359/100000000000000 : ℝ)*(f.sum) + (7180589326749/5405000000000000000000000000 : ℝ)*base66 + (1379946330710122371/270250000000000000000000000000000 : ℝ)*base67 + (1782555117110622371/270250000000000000000000000000000 : ℝ)*base69 + (2604842056369872371/270250000000000000000000000000000 : ℝ)*base71 + (2691727837171/5405000000000000000000000000 : ℝ)*base73 + (933212971738622371/270250000000000000000000000000000 : ℝ)*base75 + (1964708293246372371/270250000000000000000000000000000 : ℝ)*base77 + (1526171630287372371/270250000000000000000000000000000 : ℝ)*base79 + (9026453806813/2702500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13128693/1250000000000000000000 : ℝ)*base90 + (13128693/1250000000000000000000 : ℝ)*base92 + (13128693/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (210575932702512756790767033/23500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (870936717/50000000000000 : ℝ)*(base19) + (1629511169/100000000000000 : ℝ)*(base23) + (193059797/100000000000000 : ℝ)*(upper3) + (2783467/25000000000000 : ℝ)*(lower4) + (23472617/12500000000000 : ℝ)*(upper5) + (2107298314540237/50000000000000 : ℝ)*(major0) + (2107298314540237/50000000000000 : ℝ)*(major1) + (2107298314540237/50000000000000 : ℝ)*(major2) + (32003243707/100000000000000 : ℝ)*(sp1) + (33061474673/100000000000000 : ℝ)*(sp2) + (2840431289479937/50000000000000 : ℝ)*(sp4) + (1420207208460683/25000000000000 : ℝ)*(sp5) + (5680827887974031/100000000000000 : ℝ)*(sp6) + (13741651902559/500000000000 : ℝ)*(sp7) + (13741651902559/500000000000 : ℝ)*(f.failure) + (2840431289479937/50000000000000 : ℝ)*(f.sum) + (6470757740877/10810000000000000000000000000 : ℝ)*base66 + (12055947517142534249/1081000000000000000000000000000000 : ℝ)*base68 + (7447378009564534249/1081000000000000000000000000000000 : ℝ)*base70 + (7655035500030534249/1081000000000000000000000000000000 : ℝ)*base72 + (147042811827/10810000000000000000000000000 : ℝ)*base74 + (5051120173733534249/1081000000000000000000000000000000 : ℝ)*base76 + (4934344524996534249/1081000000000000000000000000000000 : ℝ)*base78 + (14159292527407534249/1081000000000000000000000000000000 : ℝ)*base80 + (53059309677293/10810000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (57169/12500000000000000000 : ℝ)*base89 + (57169/12500000000000000000 : ℝ)*base91 + (57169/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1307_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10999/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1307_s5_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074533753/10000000000 : ℝ)*x 0 + (5415042939/10000000000 : ℝ)*x 1 + (104859591/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074533753/10000000000 : ℝ)^4267 ≤ (12625057446587/100000000000000 : ℝ)^3243 := by
    have hnat : (2074533753 : ℕ)^4267*100000000000000^3243 ≤ 12625057446587^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074533753 10000000000 12625057446587 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415042939/10000000000 : ℝ)^4267 ≤ (356923238089/800000000000 : ℝ)^3243 := by
    have hnat : (5415042939 : ℕ)^4267*800000000000^3243 ≤ 356923238089^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415042939 10000000000 356923238089 800000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104859591/200000000 : ℝ)^4267 ≤ (4275953776483/10000000000000 : ℝ)^3243 := by
    have hnat : (104859591 : ℕ)^4267*10000000000000^3243 ≤ 4275953776483^3243*200000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104859591 200000000 4275953776483 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074533753/10000000000 : ℝ), (5415042939/10000000000 : ℝ), (104859591/200000000 : ℝ)] ![(12625057446587/100000000000000 : ℝ), (356923238089/800000000000 : ℝ), (4275953776483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074533753/10000000000 : ℝ)|^4267 ≤ (12625057446587/100000000000000 : ℝ)^3243
        have hw : |(-2074533753/10000000000 : ℝ)|=(2074533753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415042939/10000000000 : ℝ)|^4267 ≤ (356923238089/800000000000 : ℝ)^3243
        have hw : |(5415042939/10000000000 : ℝ)|=(5415042939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104859591/200000000 : ℝ)|^4267 ≤ (4275953776483/10000000000000 : ℝ)^3243
        have hw : |(104859591/200000000 : ℝ)|=(104859591/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349706621/10000000000 : ℝ)*x 0 + (-2162240441/10000000000 : ℝ)*x 1 + (5242979513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349706621/10000000000 : ℝ)^4267 ≤ (21954232094439/50000000000000 : ℝ)^3243 := by
    have hnat : (5349706621 : ℕ)^4267*50000000000000^3243 ≤ 21954232094439^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349706621 10000000000 21954232094439 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162240441/10000000000 : ℝ)^4267 ≤ (13331998423187/100000000000000 : ℝ)^3243 := by
    have hnat : (2162240441 : ℕ)^4267*100000000000000^3243 ≤ 13331998423187^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162240441 10000000000 13331998423187 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242979513/10000000000 : ℝ)^4267 ≤ (42759537367791/100000000000000 : ℝ)^3243 := by
    have hnat : (5242979513 : ℕ)^4267*100000000000000^3243 ≤ 42759537367791^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242979513 10000000000 42759537367791 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349706621/10000000000 : ℝ), (-2162240441/10000000000 : ℝ), (5242979513/10000000000 : ℝ)] ![(21954232094439/50000000000000 : ℝ), (13331998423187/100000000000000 : ℝ), (42759537367791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349706621/10000000000 : ℝ)|^4267 ≤ (21954232094439/50000000000000 : ℝ)^3243
        have hw : |(5349706621/10000000000 : ℝ)|=(5349706621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2162240441/10000000000 : ℝ)|^4267 ≤ (13331998423187/100000000000000 : ℝ)^3243
        have hw : |(-2162240441/10000000000 : ℝ)|=(2162240441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242979513/10000000000 : ℝ)|^4267 ≤ (42759537367791/100000000000000 : ℝ)^3243
        have hw : |(5242979513/10000000000 : ℝ)|=(5242979513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337426639/2500000000 : ℝ)*x 0 + (2621489791/5000000000 : ℝ)*x 1 + (-2162240437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337426639/2500000000 : ℝ)^4267 ≤ (21954231743463/50000000000000 : ℝ)^3243 := by
    have hnat : (1337426639 : ℕ)^4267*50000000000000^3243 ≤ 21954231743463^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337426639 2500000000 21954231743463 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621489791/5000000000 : ℝ)^4267 ≤ (21379769054107/50000000000000 : ℝ)^3243 := by
    have hnat : (2621489791 : ℕ)^4267*50000000000000^3243 ≤ 21379769054107^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621489791 5000000000 21379769054107 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162240437/10000000000 : ℝ)^4267 ≤ (833249899421/6250000000000 : ℝ)^3243 := by
    have hnat : (2162240437 : ℕ)^4267*6250000000000^3243 ≤ 833249899421^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162240437 10000000000 833249899421 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337426639/2500000000 : ℝ), (2621489791/5000000000 : ℝ), (-2162240437/10000000000 : ℝ)] ![(21954231743463/50000000000000 : ℝ), (21379769054107/50000000000000 : ℝ), (833249899421/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337426639/2500000000 : ℝ)|^4267 ≤ (21954231743463/50000000000000 : ℝ)^3243
        have hw : |(1337426639/2500000000 : ℝ)|=(1337426639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621489791/5000000000 : ℝ)|^4267 ≤ (21379769054107/50000000000000 : ℝ)^3243
        have hw : |(2621489791/5000000000 : ℝ)|=(2621489791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2162240437/10000000000 : ℝ)|^4267 ≤ (833249899421/6250000000000 : ℝ)^3243
        have hw : |(-2162240437/10000000000 : ℝ)|=(2162240437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335817087/10000000000 : ℝ)*x 0 + (4161449899/10000000000 : ℝ)*x 1 + (4517108907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335817087/10000000000 : ℝ)^4267 ≤ (16651124351677/50000000000000 : ℝ)^3243 := by
    have hnat : (4335817087 : ℕ)^4267*50000000000000^3243 ≤ 16651124351677^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335817087 10000000000 16651124351677 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161449899/10000000000 : ℝ)^4267 ≤ (31551390518423/100000000000000 : ℝ)^3243 := by
    have hnat : (4161449899 : ℕ)^4267*100000000000000^3243 ≤ 31551390518423^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161449899 10000000000 31551390518423 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517108907/10000000000 : ℝ)^4267 ≤ (35146360763159/100000000000000 : ℝ)^3243 := by
    have hnat : (4517108907 : ℕ)^4267*100000000000000^3243 ≤ 35146360763159^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517108907 10000000000 35146360763159 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335817087/10000000000 : ℝ), (4161449899/10000000000 : ℝ), (4517108907/10000000000 : ℝ)] ![(16651124351677/50000000000000 : ℝ), (31551390518423/100000000000000 : ℝ), (35146360763159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335817087/10000000000 : ℝ)|^4267 ≤ (16651124351677/50000000000000 : ℝ)^3243
        have hw : |(4335817087/10000000000 : ℝ)|=(4335817087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161449899/10000000000 : ℝ)|^4267 ≤ (31551390518423/100000000000000 : ℝ)^3243
        have hw : |(4161449899/10000000000 : ℝ)|=(4161449899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517108907/10000000000 : ℝ)|^4267 ≤ (35146360763159/100000000000000 : ℝ)^3243
        have hw : |(4517108907/10000000000 : ℝ)|=(4517108907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129659157/625000000 : ℝ)*x 0 + (1048719513/2000000000 : ℝ)*x 1 + (1353605437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129659157/625000000 : ℝ)^4267 ≤ (3156289903101/25000000000000 : ℝ)^3243 := by
    have hnat : (129659157 : ℕ)^4267*25000000000000^3243 ≤ 3156289903101^3243*625000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129659157 625000000 3156289903101 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048719513/2000000000 : ℝ)^4267 ≤ (8553233931931/20000000000000 : ℝ)^3243 := by
    have hnat : (1048719513 : ℕ)^4267*20000000000000^3243 ≤ 8553233931931^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048719513 2000000000 8553233931931 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353605437/2500000000 : ℝ)^4267 ≤ (892173414353/2000000000000 : ℝ)^3243 := by
    have hnat : (1353605437 : ℕ)^4267*2000000000000^3243 ≤ 892173414353^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353605437 2500000000 892173414353 2000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129659157/625000000 : ℝ), (1048719513/2000000000 : ℝ), (1353605437/2500000000 : ℝ)] ![(3156289903101/25000000000000 : ℝ), (8553233931931/20000000000000 : ℝ), (892173414353/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129659157/625000000 : ℝ)|^4267 ≤ (3156289903101/25000000000000 : ℝ)^3243
        have hw : |(-129659157/625000000 : ℝ)|=(129659157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048719513/2000000000 : ℝ)|^4267 ≤ (8553233931931/20000000000000 : ℝ)^3243
        have hw : |(1048719513/2000000000 : ℝ)|=(1048719513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353605437/2500000000 : ℝ)|^4267 ≤ (892173414353/2000000000000 : ℝ)^3243
        have hw : |(1353605437/2500000000 : ℝ)|=(1353605437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652785729/5000000000 : ℝ)*x 0 + (-497699561/2500000000 : ℝ)*x 1 + (5414421661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652785729/5000000000 : ℝ)^4267 ≤ (2171622954593/5000000000000 : ℝ)^3243 := by
    have hnat : (2652785729 : ℕ)^4267*5000000000000^3243 ≤ 2171622954593^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652785729 5000000000 2171622954593 5000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497699561/2500000000 : ℝ)^4267 ≤ (2391774223573/20000000000000 : ℝ)^3243 := by
    have hnat : (497699561 : ℕ)^4267*20000000000000^3243 ≤ 2391774223573^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497699561 2500000000 2391774223573 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414421661/10000000000 : ℝ)^4267 ≤ (44608669774541/100000000000000 : ℝ)^3243 := by
    have hnat : (5414421661 : ℕ)^4267*100000000000000^3243 ≤ 44608669774541^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414421661 10000000000 44608669774541 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652785729/5000000000 : ℝ), (-497699561/2500000000 : ℝ), (5414421661/10000000000 : ℝ)] ![(2171622954593/5000000000000 : ℝ), (2391774223573/20000000000000 : ℝ), (44608669774541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652785729/5000000000 : ℝ)|^4267 ≤ (2171622954593/5000000000000 : ℝ)^3243
        have hw : |(2652785729/5000000000 : ℝ)|=(2652785729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497699561/2500000000 : ℝ)|^4267 ≤ (2391774223573/20000000000000 : ℝ)^3243
        have hw : |(-497699561/2500000000 : ℝ)|=(497699561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414421661/10000000000 : ℝ)|^4267 ≤ (44608669774541/100000000000000 : ℝ)^3243
        have hw : |(5414421661/10000000000 : ℝ)|=(5414421661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305571339/10000000000 : ℝ)*x 0 + (27072109/50000000 : ℝ)*x 1 + (-398159643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305571339/10000000000 : ℝ)^4267 ≤ (8686491562021/20000000000000 : ℝ)^3243 := by
    have hnat : (5305571339 : ℕ)^4267*20000000000000^3243 ≤ 8686491562021^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305571339 10000000000 8686491562021 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27072109/50000000 : ℝ)^4267 ≤ (11152167820337/25000000000000 : ℝ)^3243 := by
    have hnat : (27072109 : ℕ)^4267*25000000000000^3243 ≤ 11152167820337^3243*50000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27072109 50000000 11152167820337 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398159643/2000000000 : ℝ)^4267 ≤ (5979435444327/50000000000000 : ℝ)^3243 := by
    have hnat : (398159643 : ℕ)^4267*50000000000000^3243 ≤ 5979435444327^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398159643 2000000000 5979435444327 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305571339/10000000000 : ℝ), (27072109/50000000 : ℝ), (-398159643/2000000000 : ℝ)] ![(8686491562021/20000000000000 : ℝ), (11152167820337/25000000000000 : ℝ), (5979435444327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305571339/10000000000 : ℝ)|^4267 ≤ (8686491562021/20000000000000 : ℝ)^3243
        have hw : |(5305571339/10000000000 : ℝ)|=(5305571339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27072109/50000000 : ℝ)|^4267 ≤ (11152167820337/25000000000000 : ℝ)^3243
        have hw : |(27072109/50000000 : ℝ)|=(27072109/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398159643/2000000000 : ℝ)|^4267 ≤ (5979435444327/50000000000000 : ℝ)^3243
        have hw : |(-398159643/2000000000 : ℝ)|=(398159643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s5_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335843599/10000000000 : ℝ)*x 0 + (4515831499/10000000000 : ℝ)*x 1 + (2081366919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335843599/10000000000 : ℝ)^4267 ≤ (4162814579159/12500000000000 : ℝ)^3243 := by
    have hnat : (4335843599 : ℕ)^4267*12500000000000^3243 ≤ 4162814579159^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335843599 10000000000 4162814579159 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515831499/10000000000 : ℝ)^4267 ≤ (8783320958769/25000000000000 : ℝ)^3243 := by
    have hnat : (4515831499 : ℕ)^4267*25000000000000^3243 ≤ 8783320958769^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515831499 10000000000 8783320958769 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081366919/5000000000 : ℝ)^4267 ≤ (15782099756937/50000000000000 : ℝ)^3243 := by
    have hnat : (2081366919 : ℕ)^4267*50000000000000^3243 ≤ 15782099756937^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081366919 5000000000 15782099756937 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335843599/10000000000 : ℝ), (4515831499/10000000000 : ℝ), (2081366919/5000000000 : ℝ)] ![(4162814579159/12500000000000 : ℝ), (8783320958769/25000000000000 : ℝ), (15782099756937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335843599/10000000000 : ℝ)|^4267 ≤ (4162814579159/12500000000000 : ℝ)^3243
        have hw : |(4335843599/10000000000 : ℝ)|=(4335843599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515831499/10000000000 : ℝ)|^4267 ≤ (8783320958769/25000000000000 : ℝ)^3243
        have hw : |(4515831499/10000000000 : ℝ)|=(4515831499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081366919/5000000000 : ℝ)|^4267 ≤ (15782099756937/50000000000000 : ℝ)^3243
        have hw : |(2081366919/5000000000 : ℝ)|=(2081366919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10999/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5527/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2939/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10999/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10999/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10999/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10999/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10999/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10999/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10999/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (1014524316602891/10000000000000000000 : ℝ) := by
    have hpowers : (10999/100000 : ℝ)^2133 ≤ (1014524316602891/10000000000000000000 : ℝ)^512 := by
      have hnat : (10999 : ℕ)^2133*10000000000000000000^512 ≤ 1014524316602891^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10999 100000 1014524316602891 10000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10999/100000 : ℝ)) (X := (1014524316602891/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (17239018057874183/50000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^2133 ≤ (17239018057874183/50000000000000000000 : ℝ)^512 := by
      have hnat : (14753 : ℕ)^2133*50000000000000000000^512 ≤ 17239018057874183^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 17239018057874183 50000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (17239018057874183/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001014524316602891/5000000000000000000 : ℝ) ≤ (10000487010226249/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (5001014524316602891/5000000000000000000 : ℝ)^512 ≤ (10000487010226249/10000000000000000 : ℝ)^2133 := by
      have hnat : (5001014524316602891 : ℕ)^512*10000000000000000^2133 ≤ 10000487010226249^2133*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001014524316602891 5000000000000000000 10000487010226249 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000487010226249/10000000000000000 : ℝ)) (X := (5001014524316602891/5000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011155819820444319/25000000000000000000 : ℝ) ≤ (5000535472246753/5000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (25011155819820444319/25000000000000000000 : ℝ)^512 ≤ (5000535472246753/5000000000000000 : ℝ)^2133 := by
      have hnat : (25011155819820444319 : ℕ)^512*5000000000000000^2133 ≤ 5000535472246753^2133*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011155819820444319 25000000000000000000 5000535472246753 5000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000535472246753/5000000000000000 : ℝ)) (X := (25011155819820444319/25000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017239018057874183/25000000000000000000 : ℝ) ≤ (10001654878760763/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (25017239018057874183/25000000000000000000 : ℝ)^512 ≤ (10001654878760763/10000000000000000 : ℝ)^2133 := by
      have hnat : (25017239018057874183 : ℕ)^512*10000000000000000^2133 ≤ 10001654878760763^2133*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017239018057874183 25000000000000000000 10001654878760763 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001654878760763/10000000000000000 : ℝ)) (X := (25017239018057874183/25000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1014524316602891/10000000000000000000 : ℝ) ≤ ((1876449142518910963/1877000000000000000 : ℝ)+2*(583934267257/375400000000000 : ℝ)*(10999/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (1876449142518910963/1877000000000000000 : ℝ)+2*(583934267257/375400000000000 : ℝ)*(10999/100000 : ℝ)=(10000487010226249/10000000000000000 : ℝ) by norm_num, show 1+2*(1014524316602891/10000000000000000000 : ℝ)=(5001014524316602891/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17239018057874183/50000000000000000000 : ℝ)+(1014524316602891/10000000000000000000 : ℝ) ≤ ((1876449142518910963/1877000000000000000 : ℝ)+(583934267257/375400000000000 : ℝ)*((14753/100000 : ℝ)+(10999/100000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (1876449142518910963/1877000000000000000 : ℝ)+(583934267257/375400000000000 : ℝ)*((14753/100000 : ℝ)+(10999/100000 : ℝ))=(5000535472246753/5000000000000000 : ℝ) by norm_num, show 1+(17239018057874183/50000000000000000000 : ℝ)+(1014524316602891/10000000000000000000 : ℝ)=(25011155819820444319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17239018057874183/50000000000000000000 : ℝ) ≤ ((1876449142518910963/1877000000000000000 : ℝ)+2*(583934267257/375400000000000 : ℝ)*(14753/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (1876449142518910963/1877000000000000000 : ℝ)+2*(583934267257/375400000000000 : ℝ)*(14753/100000 : ℝ)=(10001654878760763/10000000000000000 : ℝ) by norm_num, show 1+2*(17239018057874183/50000000000000000000 : ℝ)=(25017239018057874183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1876449142518910963/1877000000000000000 : ℝ)*(X 1 0+X 2 0)+(583934267257/375400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (10999/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (1876449142518910963/1877000000000000000 : ℝ)) (alpha := (583934267257/375400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1876449142518910963/1877000000000000000 : ℝ)*(X 0 1+X 2 1)+(583934267257/375400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (10999/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (1876449142518910963/1877000000000000000 : ℝ)) (alpha := (583934267257/375400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1876449142518910963/1877000000000000000 : ℝ)*(X 0 2+X 1 2)+(583934267257/375400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (10999/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (1876449142518910963/1877000000000000000 : ℝ)) (alpha := (583934267257/375400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2074533753/10000000000 : ℝ)*X 0 0+(5415042939/10000000000 : ℝ)*X 0 1+(104859591/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349706621/10000000000 : ℝ)*X 1 0+(-2162240441/10000000000 : ℝ)*X 1 1+(5242979513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337426639/2500000000 : ℝ)*X 2 0+(2621489791/5000000000 : ℝ)*X 2 1+(-2162240437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335817087/10000000000 : ℝ)*X 0 0+(4161449899/10000000000 : ℝ)*X 0 1+(4517108907/10000000000 : ℝ)*X 0 2+(4335817087/10000000000 : ℝ)*X 1 0+(4161449899/10000000000 : ℝ)*X 1 1+(4517108907/10000000000 : ℝ)*X 1 2+(4335817087/10000000000 : ℝ)*X 2 0+(4161449899/10000000000 : ℝ)*X 2 1+(4517108907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-129659157/625000000 : ℝ)*X 0 0+(1048719513/2000000000 : ℝ)*X 0 1+(1353605437/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652785729/5000000000 : ℝ)*X 1 0+(-497699561/2500000000 : ℝ)*X 1 1+(5414421661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305571339/10000000000 : ℝ)*X 2 0+(27072109/50000000 : ℝ)*X 2 1+(-398159643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335843599/10000000000 : ℝ)*X 0 0+(4515831499/10000000000 : ℝ)*X 0 1+(2081366919/5000000000 : ℝ)*X 0 2+(4335843599/10000000000 : ℝ)*X 1 0+(4515831499/10000000000 : ℝ)*X 1 1+(2081366919/5000000000 : ℝ)*X 1 2+(4335843599/10000000000 : ℝ)*X 2 0+(4515831499/10000000000 : ℝ)*X 2 1+(2081366919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (267933275651196907762811991/93850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (516605241/100000000000000 : ℝ)*(base19) + (100610563/25000000000000 : ℝ)*(base23) + (23296941/100000000000000 : ℝ)*(lower2) + (57398759/100000000000000 : ℝ)*(upper3) + (8755249/50000000000000 : ℝ)*(upper5) + (4311762232613919/100000000000000 : ℝ)*(major0) + (4311762232613919/100000000000000 : ℝ)*(major1) + (4311762232613919/100000000000000 : ℝ)*(major2) + (1452955688448551/25000000000000 : ℝ)*(sp0) + (5811831969193931/100000000000000 : ℝ)*(sp1) + (145295802083923/2500000000000 : ℝ)*(sp2) + (702921658330297/25000000000000 : ℝ)*(sp3) + (1216500621/12500000000000 : ℝ)*(sp4) + (2625471909/50000000000000 : ℝ)*(sp7) + (1405845942132503/50000000000000 : ℝ)*(f.failure) + (1452958121449793/25000000000000 : ℝ)*(f.sum) + (91909174084517/18770000000000000000000000000 : ℝ)*base66 + (534635277007408997/187700000000000000000000000000000 : ℝ)*base67 + (141158975986391003/187700000000000000000000000000000 : ℝ)*base70 + (156300777218891003/187700000000000000000000000000000 : ℝ)*base72 + (101900417173527/18770000000000000000000000000 : ℝ)*base74 + (233725734716691003/187700000000000000000000000000000 : ℝ)*base76 + (664639371480191003/187700000000000000000000000000000 : ℝ)*base78 + (351368945464608997/187700000000000000000000000000000 : ℝ)*base79 + (100838811069017/18770000000000000000000000000 : ℝ)*base82 + (6820873/1250000000000000000000 : ℝ)*base89 + (6820873/1250000000000000000000 : ℝ)*base91 + (6820873/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152379964590728728519322427/46925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117113879/20000000000000 : ℝ)*(base19) + (607034923/100000000000000 : ℝ)*(base23) + (58155139/100000000000000 : ℝ)*(upper3) + (16339551/25000000000000 : ℝ)*(lower4) + (3863401/10000000000000 : ℝ)*(upper5) + (2171511595531281/50000000000000 : ℝ)*(major0) + (2171511595531281/50000000000000 : ℝ)*(major1) + (2171511595531281/50000000000000 : ℝ)*(major2) + (2324876983/25000000000000 : ℝ)*(sp1) + (12855095077/100000000000000 : ℝ)*(sp2) + (5853969178553699/100000000000000 : ℝ)*(sp4) + (1463489823369093/25000000000000 : ℝ)*(sp5) + (5853955716423699/100000000000000 : ℝ)*(sp6) + (1416038547663897/50000000000000 : ℝ)*(sp7) + (1416038547663897/50000000000000 : ℝ)*(f.failure) + (5853969178553699/100000000000000 : ℝ)*(f.sum) + (6760795842213/9385000000000000000000000000 : ℝ)*base66 + (158455139981431397/93850000000000000000000000000000 : ℝ)*base68 + (51176432820981397/93850000000000000000000000000000 : ℝ)*base70 + (304661484711481397/93850000000000000000000000000000 : ℝ)*base72 + (22191256178207/9385000000000000000000000000 : ℝ)*base73 + (985363570711581397/93850000000000000000000000000000 : ℝ)*base76 + (274815272517731397/93850000000000000000000000000000 : ℝ)*base78 + (1189285997445581397/93850000000000000000000000000000 : ℝ)*base80 + (4013099839413/9385000000000000000000000000 : ℝ)*base82 + (3568473/1250000000000000000000 : ℝ)*base90 + (3568473/1250000000000000000000 : ℝ)*base92 + (3568473/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1307_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10999/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1307_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1307_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1307_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1307_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:15.407838+00:00
-- url     : https://prove2.me/submissions/6b6191e0-3717-4fa9-a583-94222dc738c6

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
theorem support_rectangle_w1109_s9_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091386173/5000000000 : ℝ)*x 0 + (2696785111/5000000000 : ℝ)*x 1 + (5265242703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091386173/5000000000 : ℝ)^4151 ≤ (2652059458133/20000000000000 : ℝ)^3127 := by
    have hnat : (1091386173 : ℕ)^4151*20000000000000^3127 ≤ 2652059458133^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091386173 5000000000 2652059458133 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696785111/5000000000 : ℝ)^4151 ≤ (22031485129107/50000000000000 : ℝ)^3127 := by
    have hnat : (2696785111 : ℕ)^4151*50000000000000^3127 ≤ 22031485129107^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696785111 5000000000 22031485129107 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265242703/10000000000 : ℝ)^4151 ≤ (10669183107417/25000000000000 : ℝ)^3127 := by
    have hnat : (5265242703 : ℕ)^4151*25000000000000^3127 ≤ 10669183107417^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265242703 10000000000 10669183107417 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091386173/5000000000 : ℝ), (2696785111/5000000000 : ℝ), (5265242703/10000000000 : ℝ)] ![(2652059458133/20000000000000 : ℝ), (22031485129107/50000000000000 : ℝ), (10669183107417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091386173/5000000000 : ℝ)|^4151 ≤ (2652059458133/20000000000000 : ℝ)^3127
        have hw : |(-1091386173/5000000000 : ℝ)|=(1091386173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696785111/5000000000 : ℝ)|^4151 ≤ (22031485129107/50000000000000 : ℝ)^3127
        have hw : |(2696785111/5000000000 : ℝ)|=(2696785111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265242703/10000000000 : ℝ)|^4151 ≤ (10669183107417/25000000000000 : ℝ)^3127
        have hw : |(5265242703/10000000000 : ℝ)|=(5265242703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s9_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336213931/2500000000 : ℝ)*x 0 + (-1123934989/5000000000 : ℝ)*x 1 + (5265242703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336213931/2500000000 : ℝ)^4151 ≤ (10883863309459/25000000000000 : ℝ)^3127 := by
    have hnat : (1336213931 : ℕ)^4151*25000000000000^3127 ≤ 10883863309459^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336213931 2500000000 10883863309459 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123934989/5000000000 : ℝ)^4151 ≤ (6893907158897/50000000000000 : ℝ)^3127 := by
    have hnat : (1123934989 : ℕ)^4151*50000000000000^3127 ≤ 6893907158897^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123934989 5000000000 6893907158897 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265242703/10000000000 : ℝ)^4151 ≤ (10669183107417/25000000000000 : ℝ)^3127 := by
    have hnat : (5265242703 : ℕ)^4151*25000000000000^3127 ≤ 10669183107417^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265242703 10000000000 10669183107417 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336213931/2500000000 : ℝ), (-1123934989/5000000000 : ℝ), (5265242703/10000000000 : ℝ)] ![(10883863309459/25000000000000 : ℝ), (6893907158897/50000000000000 : ℝ), (10669183107417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336213931/2500000000 : ℝ)|^4151 ≤ (10883863309459/25000000000000 : ℝ)^3127
        have hw : |(1336213931/2500000000 : ℝ)|=(1336213931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123934989/5000000000 : ℝ)|^4151 ≤ (6893907158897/50000000000000 : ℝ)^3127
        have hw : |(-1123934989/5000000000 : ℝ)|=(1123934989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265242703/10000000000 : ℝ)|^4151 ≤ (10669183107417/25000000000000 : ℝ)^3127
        have hw : |(5265242703/10000000000 : ℝ)|=(5265242703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s9_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336213931/2500000000 : ℝ)*x 0 + (5265242703/10000000000 : ℝ)*x 1 + (-1123934989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336213931/2500000000 : ℝ)^4151 ≤ (10883863309459/25000000000000 : ℝ)^3127 := by
    have hnat : (1336213931 : ℕ)^4151*25000000000000^3127 ≤ 10883863309459^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336213931 2500000000 10883863309459 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265242703/10000000000 : ℝ)^4151 ≤ (10669183107417/25000000000000 : ℝ)^3127 := by
    have hnat : (5265242703 : ℕ)^4151*25000000000000^3127 ≤ 10669183107417^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265242703 10000000000 10669183107417 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123934989/5000000000 : ℝ)^4151 ≤ (6893907158897/50000000000000 : ℝ)^3127 := by
    have hnat : (1123934989 : ℕ)^4151*50000000000000^3127 ≤ 6893907158897^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123934989 5000000000 6893907158897 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336213931/2500000000 : ℝ), (5265242703/10000000000 : ℝ), (-1123934989/5000000000 : ℝ)] ![(10883863309459/25000000000000 : ℝ), (10669183107417/25000000000000 : ℝ), (6893907158897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336213931/2500000000 : ℝ)|^4151 ≤ (10883863309459/25000000000000 : ℝ)^3127
        have hw : |(1336213931/2500000000 : ℝ)|=(1336213931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265242703/10000000000 : ℝ)|^4151 ≤ (10669183107417/25000000000000 : ℝ)^3127
        have hw : |(5265242703/10000000000 : ℝ)|=(5265242703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123934989/5000000000 : ℝ)|^4151 ≤ (6893907158897/50000000000000 : ℝ)^3127
        have hw : |(-1123934989/5000000000 : ℝ)|=(1123934989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s9_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273084101/625000000 : ℝ)*x 0 + (1061091277/2500000000 : ℝ)*x 1 + (1124504479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273084101/625000000 : ℝ)^4151 ≤ (3331680955451/10000000000000 : ℝ)^3127 := by
    have hnat : (273084101 : ℕ)^4151*10000000000000^3127 ≤ 3331680955451^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273084101 625000000 3331680955451 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061091277/2500000000 : ℝ)^4151 ≤ (8014426030681/25000000000000 : ℝ)^3127 := by
    have hnat : (1061091277 : ℕ)^4151*25000000000000^3127 ≤ 8014426030681^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061091277 2500000000 8014426030681 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124504479/2500000000 : ℝ)^4151 ≤ (3462548630821/10000000000000 : ℝ)^3127 := by
    have hnat : (1124504479 : ℕ)^4151*10000000000000^3127 ≤ 3462548630821^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124504479 2500000000 3462548630821 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273084101/625000000 : ℝ), (1061091277/2500000000 : ℝ), (1124504479/2500000000 : ℝ)] ![(3331680955451/10000000000000 : ℝ), (8014426030681/25000000000000 : ℝ), (3462548630821/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273084101/625000000 : ℝ)|^4151 ≤ (3331680955451/10000000000000 : ℝ)^3127
        have hw : |(273084101/625000000 : ℝ)|=(273084101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061091277/2500000000 : ℝ)|^4151 ≤ (8014426030681/25000000000000 : ℝ)^3127
        have hw : |(1061091277/2500000000 : ℝ)|=(1061091277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124504479/2500000000 : ℝ)|^4151 ≤ (3462548630821/10000000000000 : ℝ)^3127
        have hw : |(1124504479/2500000000 : ℝ)|=(1124504479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s9_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-436555459/2000000000 : ℝ)*x 0 + (210622579/400000000 : ℝ)*x 1 + (5393247291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436555459/2000000000 : ℝ)^4151 ≤ (1657542150147/12500000000000 : ℝ)^3127 := by
    have hnat : (436555459 : ℕ)^4151*12500000000000^3127 ≤ 1657542150147^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436555459 2000000000 1657542150147 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210622579/400000000 : ℝ)^4151 ≤ (666878040847/1562500000000 : ℝ)^3127 := by
    have hnat : (210622579 : ℕ)^4151*1562500000000^3127 ≤ 666878040847^3127*400000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210622579 400000000 666878040847 1562500000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393247291/10000000000 : ℝ)^4151 ≤ (2753716760281/6250000000000 : ℝ)^3127 := by
    have hnat : (5393247291 : ℕ)^4151*6250000000000^3127 ≤ 2753716760281^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393247291 10000000000 2753716760281 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436555459/2000000000 : ℝ), (210622579/400000000 : ℝ), (5393247291/10000000000 : ℝ)] ![(1657542150147/12500000000000 : ℝ), (666878040847/1562500000000 : ℝ), (2753716760281/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436555459/2000000000 : ℝ)|^4151 ≤ (1657542150147/12500000000000 : ℝ)^3127
        have hw : |(-436555459/2000000000 : ℝ)|=(436555459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210622579/400000000 : ℝ)|^4151 ≤ (666878040847/1562500000000 : ℝ)^3127
        have hw : |(210622579/400000000 : ℝ)|=(210622579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393247291/10000000000 : ℝ)|^4151 ≤ (2753716760281/6250000000000 : ℝ)^3127
        have hw : |(5393247291/10000000000 : ℝ)|=(5393247291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s9_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369355403/10000000000 : ℝ)*x 0 + (281086369/625000000 : ℝ)*x 1 + (2122501707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369355403/10000000000 : ℝ)^4151 ≤ (33316908619821/100000000000000 : ℝ)^3127 := by
    have hnat : (4369355403 : ℕ)^4151*100000000000000^3127 ≤ 33316908619821^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369355403 10000000000 33316908619821 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281086369/625000000 : ℝ)^4151 ≤ (8654746796111/25000000000000 : ℝ)^3127 := by
    have hnat : (281086369 : ℕ)^4151*25000000000000^3127 ≤ 8654746796111^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281086369 625000000 8654746796111 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122501707/5000000000 : ℝ)^4151 ≤ (3206410418431/10000000000000 : ℝ)^3127 := by
    have hnat : (2122501707 : ℕ)^4151*10000000000000^3127 ≤ 3206410418431^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122501707 5000000000 3206410418431 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369355403/10000000000 : ℝ), (281086369/625000000 : ℝ), (2122501707/5000000000 : ℝ)] ![(33316908619821/100000000000000 : ℝ), (8654746796111/25000000000000 : ℝ), (3206410418431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369355403/10000000000 : ℝ)|^4151 ≤ (33316908619821/100000000000000 : ℝ)^3127
        have hw : |(4369355403/10000000000 : ℝ)|=(4369355403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281086369/625000000 : ℝ)|^4151 ≤ (8654746796111/25000000000000 : ℝ)^3127
        have hw : |(281086369/625000000 : ℝ)|=(281086369/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122501707/5000000000 : ℝ)|^4151 ≤ (3206410418431/10000000000000 : ℝ)^3127
        have hw : |(2122501707/5000000000 : ℝ)|=(2122501707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1131/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1131/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1131/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1131/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1131/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1131/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1131/10000 : ℝ) ^ (8301/2048 : ℝ) ≤ (14570457393773451/100000000000000000000 : ℝ) := by
    have hpowers : (1131/10000 : ℝ)^8301 ≤ (14570457393773451/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1131 : ℕ)^8301*100000000000000000000^2048 ≤ 14570457393773451^2048*10000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1131 10000 14570457393773451 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1131/10000 : ℝ)) (X := (14570457393773451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (4361334229487221/12500000000000000000 : ℝ) := by
    have hpowers : (14029/100000 : ℝ)^8301 ≤ (4361334229487221/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14029 : ℕ)^8301*12500000000000000000^2048 ≤ 4361334229487221^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 100000 4361334229487221 12500000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/100000 : ℝ)) (X := (4361334229487221/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014570457393773451/50000000000000000000 : ℝ) ≤ (10000718877776809/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50014570457393773451/50000000000000000000 : ℝ)^2048 ≤ (10000718877776809/10000000000000000 : ℝ)^8301 := by
      have hnat : (50014570457393773451 : ℕ)^2048*10000000000000000^8301 ≤ 10000718877776809^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014570457393773451 50000000000000000000 10000718877776809 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000718877776809/10000000000000000 : ℝ)) (X := (50014570457393773451/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049461131229671219/100000000000000000000 : ℝ) ≤ (10001220064228359/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (100049461131229671219/100000000000000000000 : ℝ)^2048 ≤ (10001220064228359/10000000000000000 : ℝ)^8301 := by
      have hnat : (100049461131229671219 : ℕ)^2048*10000000000000000^8301 ≤ 10001220064228359^8301*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049461131229671219 100000000000000000000 10001220064228359 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001220064228359/10000000000000000 : ℝ)) (X := (100049461131229671219/100000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254361334229487221/6250000000000000000 : ℝ) ≤ (10001721250679909/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (6254361334229487221/6250000000000000000 : ℝ)^2048 ≤ (10001721250679909/10000000000000000 : ℝ)^8301 := by
      have hnat : (6254361334229487221 : ℕ)^2048*10000000000000000^8301 ≤ 10001721250679909^8301*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254361334229487221 6250000000000000000 10001721250679909 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001721250679909/10000000000000000 : ℝ)) (X := (6254361334229487221/6250000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14570457393773451/100000000000000000000 : ℝ) ≤ ((27180617791141082671/27190000000000000000 : ℝ)+2*(10023729031/5438000000000 : ℝ)*(1131/10000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (27180617791141082671/27190000000000000000 : ℝ)+2*(10023729031/5438000000000 : ℝ)*(1131/10000 : ℝ)=(10000718877776809/10000000000000000 : ℝ) by norm_num, show 1+2*(14570457393773451/100000000000000000000 : ℝ)=(50014570457393773451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4361334229487221/12500000000000000000 : ℝ)+(14570457393773451/100000000000000000000 : ℝ) ≤ ((27180617791141082671/27190000000000000000 : ℝ)+(10023729031/5438000000000 : ℝ)*((14029/100000 : ℝ)+(1131/10000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (27180617791141082671/27190000000000000000 : ℝ)+(10023729031/5438000000000 : ℝ)*((14029/100000 : ℝ)+(1131/10000 : ℝ))=(10001220064228359/10000000000000000 : ℝ) by norm_num, show 1+(4361334229487221/12500000000000000000 : ℝ)+(14570457393773451/100000000000000000000 : ℝ)=(100049461131229671219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4361334229487221/12500000000000000000 : ℝ) ≤ ((27180617791141082671/27190000000000000000 : ℝ)+2*(10023729031/5438000000000 : ℝ)*(14029/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (27180617791141082671/27190000000000000000 : ℝ)+2*(10023729031/5438000000000 : ℝ)*(14029/100000 : ℝ)=(10001721250679909/10000000000000000 : ℝ) by norm_num, show 1+2*(4361334229487221/12500000000000000000 : ℝ)=(6254361334229487221/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27180617791141082671/27190000000000000000 : ℝ)*(X 1 0+X 2 0)+(10023729031/5438000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27180617791141082671/27190000000000000000 : ℝ)) (alpha := (10023729031/5438000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27180617791141082671/27190000000000000000 : ℝ)*(X 0 1+X 2 1)+(10023729031/5438000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27180617791141082671/27190000000000000000 : ℝ)) (alpha := (10023729031/5438000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27180617791141082671/27190000000000000000 : ℝ)*(X 0 2+X 1 2)+(10023729031/5438000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27180617791141082671/27190000000000000000 : ℝ)) (alpha := (10023729031/5438000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091386173/5000000000 : ℝ)*X 0 0+(2696785111/5000000000 : ℝ)*X 0 1+(5265242703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336213931/2500000000 : ℝ)*X 1 0+(-1123934989/5000000000 : ℝ)*X 1 1+(5265242703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336213931/2500000000 : ℝ)*X 2 0+(5265242703/10000000000 : ℝ)*X 2 1+(-1123934989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273084101/625000000 : ℝ)*X 0 0+(1061091277/2500000000 : ℝ)*X 0 1+(1124504479/2500000000 : ℝ)*X 0 2+(273084101/625000000 : ℝ)*X 1 0+(1061091277/2500000000 : ℝ)*X 1 1+(1124504479/2500000000 : ℝ)*X 1 2+(273084101/625000000 : ℝ)*X 2 0+(1061091277/2500000000 : ℝ)*X 2 1+(1124504479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436555459/2000000000 : ℝ)*X 0 0+(210622579/400000000 : ℝ)*X 0 1+(5393247291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4369355403/10000000000 : ℝ)*X 0 0+(281086369/625000000 : ℝ)*X 0 1+(2122501707/5000000000 : ℝ)*X 0 2+(4369355403/10000000000 : ℝ)*X 1 0+(281086369/625000000 : ℝ)*X 1 1+(2122501707/5000000000 : ℝ)*X 1 2+(4369355403/10000000000 : ℝ)*X 2 0+(281086369/625000000 : ℝ)*X 2 1+(2122501707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63545365279825134017970027/33987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (378151347/100000000000000 : ℝ)*(base19) + (351528539/100000000000000 : ℝ)*(base23) + (3557377/25000000000000 : ℝ)*(lower2) + (24160221/50000000000000 : ℝ)*(upper3) + (28569177/100000000000000 : ℝ)*(upper5) + (293374729658421/5000000000000 : ℝ)*(major0) + (293374729658421/5000000000000 : ℝ)*(major1) + (293374729658421/5000000000000 : ℝ)*(major2) + (1558514312778743/20000000000000 : ℝ)*(sp0) + (1558516279654091/20000000000000 : ℝ)*(sp1) + (487036339055829/6250000000000 : ℝ)*(sp2) + (3942401751763427/100000000000000 : ℝ)*(sp3) + (10212528087/100000000000000 : ℝ)*(sp4) + (559582931/10000000000000 : ℝ)*(sp5) + (1971203673796369/50000000000000 : ℝ)*(f.failure) + (3896290888210901/50000000000000 : ℝ)*(f.sum) + (5424429761067/2719000000000000000000000000 : ℝ)*base65 + (882329177081872491/135950000000000000000000000000000 : ℝ)*base67 + (749530359005022491/135950000000000000000000000000000 : ℝ)*base69 + (957576554374422491/135950000000000000000000000000000 : ℝ)*base71 + (1189486846977/1359500000000000000000000000 : ℝ)*base74 + (3555026384492172491/135950000000000000000000000000000 : ℝ)*base75 + (1899355399434222491/135950000000000000000000000000000 : ℝ)*base77 + (1073445964523277509/135950000000000000000000000000000 : ℝ)*base80 + (3295667471/2124218750000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (25973143/5000000000000000000000 : ℝ)*base89 + (25973143/5000000000000000000000 : ℝ)*base91 + (25973143/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1109_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_box_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-513694817/2500000000 : ℝ)*x 0 + (5376774889/10000000000 : ℝ)*x 1 + (5376774801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513694817/2500000000 : ℝ)^4151 ≤ (764884951407/6250000000000 : ℝ)^3127 := by
    have hnat : (513694817 : ℕ)^4151*6250000000000^3127 ≤ 764884951407^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513694817 2500000000 764884951407 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376774889/10000000000 : ℝ)^4151 ≤ (43880920854589/100000000000000 : ℝ)^3127 := by
    have hnat : (5376774889 : ℕ)^4151*100000000000000^3127 ≤ 43880920854589^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376774889 10000000000 43880920854589 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376774801/10000000000 : ℝ)^4151 ≤ (43880919901219/100000000000000 : ℝ)^3127 := by
    have hnat : (5376774801 : ℕ)^4151*100000000000000^3127 ≤ 43880919901219^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376774801 10000000000 43880919901219 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513694817/2500000000 : ℝ), (5376774889/10000000000 : ℝ), (5376774801/10000000000 : ℝ)] ![(764884951407/6250000000000 : ℝ), (43880920854589/100000000000000 : ℝ), (43880919901219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513694817/2500000000 : ℝ)|^4151 ≤ (764884951407/6250000000000 : ℝ)^3127
        have hw : |(-513694817/2500000000 : ℝ)|=(513694817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376774889/10000000000 : ℝ)|^4151 ≤ (43880920854589/100000000000000 : ℝ)^3127
        have hw : |(5376774889/10000000000 : ℝ)|=(5376774889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376774801/10000000000 : ℝ)|^4151 ≤ (43880919901219/100000000000000 : ℝ)^3127
        have hw : |(5376774801/10000000000 : ℝ)|=(5376774801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323916429/2500000000 : ℝ)*x 0 + (-17317543/80000000 : ℝ)*x 1 + (1344193739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323916429/2500000000 : ℝ)^4151 ≤ (21502191146461/50000000000000 : ℝ)^3127 := by
    have hnat : (1323916429 : ℕ)^4151*50000000000000^3127 ≤ 21502191146461^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323916429 2500000000 21502191146461 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17317543/80000000 : ℝ)^4151 ≤ (204917126669/1562500000000 : ℝ)^3127 := by
    have hnat : (17317543 : ℕ)^4151*1562500000000^3127 ≤ 204917126669^3127*80000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17317543 80000000 204917126669 1562500000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344193739/2500000000 : ℝ)^4151 ≤ (877618431609/2000000000000 : ℝ)^3127 := by
    have hnat : (1344193739 : ℕ)^4151*2000000000000^3127 ≤ 877618431609^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344193739 2500000000 877618431609 2000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323916429/2500000000 : ℝ), (-17317543/80000000 : ℝ), (1344193739/2500000000 : ℝ)] ![(21502191146461/50000000000000 : ℝ), (204917126669/1562500000000 : ℝ), (877618431609/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323916429/2500000000 : ℝ)|^4151 ≤ (21502191146461/50000000000000 : ℝ)^3127
        have hw : |(1323916429/2500000000 : ℝ)|=(1323916429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17317543/80000000 : ℝ)|^4151 ≤ (204917126669/1562500000000 : ℝ)^3127
        have hw : |(-17317543/80000000 : ℝ)|=(17317543/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344193739/2500000000 : ℝ)|^4151 ≤ (877618431609/2000000000000 : ℝ)^3127
        have hw : |(1344193739/2500000000 : ℝ)|=(1344193739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295665849/10000000000 : ℝ)*x 0 + (5376774703/10000000000 : ℝ)*x 1 + (-2164693039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295665849/10000000000 : ℝ)^4151 ≤ (671943495729/1562500000000 : ℝ)^3127 := by
    have hnat : (5295665849 : ℕ)^4151*1562500000000^3127 ≤ 671943495729^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295665849 10000000000 671943495729 1562500000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376774703/10000000000 : ℝ)^4151 ≤ (5485114854939/12500000000000 : ℝ)^3127 := by
    have hnat : (5376774703 : ℕ)^4151*12500000000000^3127 ≤ 5485114854939^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376774703 10000000000 5485114854939 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164693039/10000000000 : ℝ)^4151 ≤ (13114697425773/100000000000000 : ℝ)^3127 := by
    have hnat : (2164693039 : ℕ)^4151*100000000000000^3127 ≤ 13114697425773^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164693039 10000000000 13114697425773 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295665849/10000000000 : ℝ), (5376774703/10000000000 : ℝ), (-2164693039/10000000000 : ℝ)] ![(671943495729/1562500000000 : ℝ), (5485114854939/12500000000000 : ℝ), (13114697425773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295665849/10000000000 : ℝ)|^4151 ≤ (671943495729/1562500000000 : ℝ)^3127
        have hw : |(5295665849/10000000000 : ℝ)|=(5295665849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376774703/10000000000 : ℝ)|^4151 ≤ (5485114854939/12500000000000 : ℝ)^3127
        have hw : |(5376774703/10000000000 : ℝ)|=(5376774703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2164693039/10000000000 : ℝ)|^4151 ≤ (13114697425773/100000000000000 : ℝ)^3127
        have hw : |(-2164693039/10000000000 : ℝ)|=(2164693039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238622303/5000000000 : ℝ)*x 0 + (4317526703/10000000000 : ℝ)*x 1 + (539690899/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238622303/5000000000 : ℝ)^4151 ≤ (4301671108103/12500000000000 : ℝ)^3127 := by
    have hnat : (2238622303 : ℕ)^4151*12500000000000^3127 ≤ 4301671108103^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238622303 5000000000 4301671108103 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317526703/10000000000 : ℝ)^4151 ≤ (32793313094543/100000000000000 : ℝ)^3127 := by
    have hnat : (4317526703 : ℕ)^4151*100000000000000^3127 ≤ 32793313094543^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317526703 10000000000 32793313094543 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539690899/1250000000 : ℝ)^4151 ≤ (8198329506241/25000000000000 : ℝ)^3127 := by
    have hnat : (539690899 : ℕ)^4151*25000000000000^3127 ≤ 8198329506241^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539690899 1250000000 8198329506241 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238622303/5000000000 : ℝ), (4317526703/10000000000 : ℝ), (539690899/1250000000 : ℝ)] ![(4301671108103/12500000000000 : ℝ), (32793313094543/100000000000000 : ℝ), (8198329506241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238622303/5000000000 : ℝ)|^4151 ≤ (4301671108103/12500000000000 : ℝ)^3127
        have hw : |(2238622303/5000000000 : ℝ)|=(2238622303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4317526703/10000000000 : ℝ)|^4151 ≤ (32793313094543/100000000000000 : ℝ)^3127
        have hw : |(4317526703/10000000000 : ℝ)|=(4317526703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539690899/1250000000 : ℝ)|^4151 ≤ (8198329506241/25000000000000 : ℝ)^3127
        have hw : |(539690899/1250000000 : ℝ)|=(539690899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1156071847/5000000000 : ℝ)*x 0 + (5280708177/10000000000 : ℝ)*x 1 + (2640353263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1156071847/5000000000 : ℝ)^4151 ≤ (2862717438419/20000000000000 : ℝ)^3127 := by
    have hnat : (1156071847 : ℕ)^4151*20000000000000^3127 ≤ 2862717438419^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156071847 5000000000 2862717438419 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280708177/10000000000 : ℝ)^4151 ≤ (42843215291427/100000000000000 : ℝ)^3127 := by
    have hnat : (5280708177 : ℕ)^4151*100000000000000^3127 ≤ 42843215291427^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280708177 10000000000 42843215291427 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640353263/5000000000 : ℝ)^4151 ≤ (21421598755099/50000000000000 : ℝ)^3127 := by
    have hnat : (2640353263 : ℕ)^4151*50000000000000^3127 ≤ 21421598755099^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640353263 5000000000 21421598755099 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1156071847/5000000000 : ℝ), (5280708177/10000000000 : ℝ), (2640353263/5000000000 : ℝ)] ![(2862717438419/20000000000000 : ℝ), (42843215291427/100000000000000 : ℝ), (21421598755099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1156071847/5000000000 : ℝ)|^4151 ≤ (2862717438419/20000000000000 : ℝ)^3127
        have hw : |(-1156071847/5000000000 : ℝ)|=(1156071847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280708177/10000000000 : ℝ)|^4151 ≤ (42843215291427/100000000000000 : ℝ)^3127
        have hw : |(5280708177/10000000000 : ℝ)|=(5280708177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640353263/5000000000 : ℝ)|^4151 ≤ (21421598755099/50000000000000 : ℝ)^3127
        have hw : |(2640353263/5000000000 : ℝ)|=(2640353263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670448451/1250000000 : ℝ)*x 0 + (-1101191671/5000000000 : ℝ)*x 1 + (211228307/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670448451/1250000000 : ℝ)^4151 ≤ (8747622115959/20000000000000 : ℝ)^3127 := by
    have hnat : (670448451 : ℕ)^4151*20000000000000^3127 ≤ 8747622115959^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670448451 1250000000 8747622115959 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101191671/5000000000 : ℝ)^4151 ≤ (13418679519079/100000000000000 : ℝ)^3127 := by
    have hnat : (1101191671 : ℕ)^4151*100000000000000^3127 ≤ 13418679519079^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101191671 5000000000 13418679519079 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211228307/400000000 : ℝ)^4151 ≤ (42843209884899/100000000000000 : ℝ)^3127 := by
    have hnat : (211228307 : ℕ)^4151*100000000000000^3127 ≤ 42843209884899^3127*400000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211228307 400000000 42843209884899 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670448451/1250000000 : ℝ), (-1101191671/5000000000 : ℝ), (211228307/400000000 : ℝ)] ![(8747622115959/20000000000000 : ℝ), (13418679519079/100000000000000 : ℝ), (42843209884899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670448451/1250000000 : ℝ)|^4151 ≤ (8747622115959/20000000000000 : ℝ)^3127
        have hw : |(670448451/1250000000 : ℝ)|=(670448451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101191671/5000000000 : ℝ)|^4151 ≤ (13418679519079/100000000000000 : ℝ)^3127
        have hw : |(-1101191671/5000000000 : ℝ)|=(1101191671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211228307/400000000 : ℝ)|^4151 ≤ (42843209884899/100000000000000 : ℝ)^3127
        have hw : |(211228307/400000000 : ℝ)|=(211228307/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670448469/1250000000 : ℝ)*x 0 + (5280707499/10000000000 : ℝ)*x 1 + (-275297923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670448469/1250000000 : ℝ)^4151 ≤ (43738112138601/100000000000000 : ℝ)^3127 := by
    have hnat : (670448469 : ℕ)^4151*100000000000000^3127 ≤ 43738112138601^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670448469 1250000000 43738112138601 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280707499/10000000000 : ℝ)^4151 ≤ (5355400998673/12500000000000 : ℝ)^3127 := by
    have hnat : (5280707499 : ℕ)^4151*12500000000000^3127 ≤ 5355400998673^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280707499 10000000000 5355400998673 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275297923/1250000000 : ℝ)^4151 ≤ (1677334982347/12500000000000 : ℝ)^3127 := by
    have hnat : (275297923 : ℕ)^4151*12500000000000^3127 ≤ 1677334982347^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275297923 1250000000 1677334982347 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670448469/1250000000 : ℝ), (5280707499/10000000000 : ℝ), (-275297923/1250000000 : ℝ)] ![(43738112138601/100000000000000 : ℝ), (5355400998673/12500000000000 : ℝ), (1677334982347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670448469/1250000000 : ℝ)|^4151 ≤ (43738112138601/100000000000000 : ℝ)^3127
        have hw : |(670448469/1250000000 : ℝ)|=(670448469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280707499/10000000000 : ℝ)|^4151 ≤ (5355400998673/12500000000000 : ℝ)^3127
        have hw : |(5280707499/10000000000 : ℝ)|=(5280707499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275297923/1250000000 : ℝ)|^4151 ≤ (1677334982347/12500000000000 : ℝ)^3127
        have hw : |(-275297923/1250000000 : ℝ)|=(275297923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266318673/625000000 : ℝ)*x 0 + (4425578879/10000000000 : ℝ)*x 1 + (4425578651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266318673/625000000 : ℝ)^4151 ≤ (32225590511781/100000000000000 : ℝ)^3127 := by
    have hnat : (266318673 : ℕ)^4151*100000000000000^3127 ≤ 32225590511781^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266318673 625000000 32225590511781 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4425578879/10000000000 : ℝ)^4151 ≤ (8471801474817/25000000000000 : ℝ)^3127 := by
    have hnat : (4425578879 : ℕ)^4151*25000000000000^3127 ≤ 8471801474817^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425578879 10000000000 8471801474817 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4425578651/10000000000 : ℝ)^4151 ≤ (16943601790869/50000000000000 : ℝ)^3127 := by
    have hnat : (4425578651 : ℕ)^4151*50000000000000^3127 ≤ 16943601790869^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425578651 10000000000 16943601790869 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266318673/625000000 : ℝ), (4425578879/10000000000 : ℝ), (4425578651/10000000000 : ℝ)] ![(32225590511781/100000000000000 : ℝ), (8471801474817/25000000000000 : ℝ), (16943601790869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266318673/625000000 : ℝ)|^4151 ≤ (32225590511781/100000000000000 : ℝ)^3127
        have hw : |(266318673/625000000 : ℝ)|=(266318673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4425578879/10000000000 : ℝ)|^4151 ≤ (8471801474817/25000000000000 : ℝ)^3127
        have hw : |(4425578879/10000000000 : ℝ)|=(4425578879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4425578651/10000000000 : ℝ)|^4151 ≤ (16943601790869/50000000000000 : ℝ)^3127
        have hw : |(4425578651/10000000000 : ℝ)|=(4425578651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_8 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2258363771/10000000000 : ℝ)*x 0 + (2607717931/5000000000 : ℝ)*x 1 + (1346595117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2258363771/10000000000 : ℝ)^4151 ≤ (13873323562913/100000000000000 : ℝ)^3127 := by
    have hnat : (2258363771 : ℕ)^4151*100000000000000^3127 ≤ 13873323562913^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258363771 10000000000 13873323562913 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607717931/5000000000 : ℝ)^4151 ≤ (42141660711173/100000000000000 : ℝ)^3127 := by
    have hnat : (2607717931 : ℕ)^4151*100000000000000^3127 ≤ 42141660711173^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607717931 5000000000 42141660711173 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346595117/2500000000 : ℝ)^4151 ≤ (351880125641/800000000000 : ℝ)^3127 := by
    have hnat : (1346595117 : ℕ)^4151*800000000000^3127 ≤ 351880125641^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346595117 2500000000 351880125641 800000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2258363771/10000000000 : ℝ), (2607717931/5000000000 : ℝ), (1346595117/2500000000 : ℝ)] ![(13873323562913/100000000000000 : ℝ), (42141660711173/100000000000000 : ℝ), (351880125641/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2258363771/10000000000 : ℝ)|^4151 ≤ (13873323562913/100000000000000 : ℝ)^3127
        have hw : |(-2258363771/10000000000 : ℝ)|=(2258363771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607717931/5000000000 : ℝ)|^4151 ≤ (42141660711173/100000000000000 : ℝ)^3127
        have hw : |(2607717931/5000000000 : ℝ)|=(2607717931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346595117/2500000000 : ℝ)|^4151 ≤ (351880125641/800000000000 : ℝ)^3127
        have hw : |(1346595117/2500000000 : ℝ)|=(1346595117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_9 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288871257/10000000000 : ℝ)*x 0 + (-2160853573/10000000000 : ℝ)*x 1 + (1346595181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288871257/10000000000 : ℝ)^4151 ≤ (42931153712559/100000000000000 : ℝ)^3127 := by
    have hnat : (5288871257 : ℕ)^4151*100000000000000^3127 ≤ 42931153712559^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288871257 10000000000 42931153712559 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160853573/10000000000 : ℝ)^4151 ≤ (13083827794681/100000000000000 : ℝ)^3127 := by
    have hnat : (2160853573 : ℕ)^4151*100000000000000^3127 ≤ 13083827794681^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160853573 10000000000 13083827794681 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346595181/2500000000 : ℝ)^4151 ≤ (21992509240093/50000000000000 : ℝ)^3127 := by
    have hnat : (1346595181 : ℕ)^4151*50000000000000^3127 ≤ 21992509240093^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346595181 2500000000 21992509240093 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288871257/10000000000 : ℝ), (-2160853573/10000000000 : ℝ), (1346595181/2500000000 : ℝ)] ![(42931153712559/100000000000000 : ℝ), (13083827794681/100000000000000 : ℝ), (21992509240093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288871257/10000000000 : ℝ)|^4151 ≤ (42931153712559/100000000000000 : ℝ)^3127
        have hw : |(5288871257/10000000000 : ℝ)|=(5288871257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2160853573/10000000000 : ℝ)|^4151 ≤ (13083827794681/100000000000000 : ℝ)^3127
        have hw : |(-2160853573/10000000000 : ℝ)|=(2160853573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346595181/2500000000 : ℝ)|^4151 ≤ (21992509240093/50000000000000 : ℝ)^3127
        have hw : |(1346595181/2500000000 : ℝ)|=(1346595181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_10 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288870939/10000000000 : ℝ)*x 0 + (269318997/500000000 : ℝ)*x 1 + (-135053441/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288870939/10000000000 : ℝ)^4151 ≤ (42931150285973/100000000000000 : ℝ)^3127 := by
    have hnat : (5288870939 : ℕ)^4151*100000000000000^3127 ≤ 42931150285973^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288870939 10000000000 42931150285973 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269318997/500000000 : ℝ)^4151 ≤ (43985009981561/100000000000000 : ℝ)^3127 := by
    have hnat : (269318997 : ℕ)^4151*100000000000000^3127 ≤ 43985009981561^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269318997 500000000 43985009981561 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135053441/625000000 : ℝ)^4151 ≤ (13083839714661/100000000000000 : ℝ)^3127 := by
    have hnat : (135053441 : ℕ)^4151*100000000000000^3127 ≤ 13083839714661^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135053441 625000000 13083839714661 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288870939/10000000000 : ℝ), (269318997/500000000 : ℝ), (-135053441/625000000 : ℝ)] ![(42931150285973/100000000000000 : ℝ), (43985009981561/100000000000000 : ℝ), (13083839714661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288870939/10000000000 : ℝ)|^4151 ≤ (42931150285973/100000000000000 : ℝ)^3127
        have hw : |(5288870939/10000000000 : ℝ)|=(5288870939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269318997/500000000 : ℝ)|^4151 ≤ (43985009981561/100000000000000 : ℝ)^3127
        have hw : |(269318997/500000000 : ℝ)|=(269318997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135053441/625000000 : ℝ)|^4151 ≤ (13083839714661/100000000000000 : ℝ)^3127
        have hw : |(-135053441/625000000 : ℝ)|=(135053441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_11 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (70290357/156250000 : ℝ)*x 0 + (4306717461/10000000000 : ℝ)*x 1 + (86134343/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70290357/156250000 : ℝ)^4151 ≤ (34631259349441/100000000000000 : ℝ)^3127 := by
    have hnat : (70290357 : ℕ)^4151*100000000000000^3127 ≤ 34631259349441^3127*156250000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70290357 156250000 34631259349441 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4306717461/10000000000 : ℝ)^4151 ≤ (16342185942661/50000000000000 : ℝ)^3127 := by
    have hnat : (4306717461 : ℕ)^4151*50000000000000^3127 ≤ 16342185942661^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306717461 10000000000 16342185942661 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86134343/200000000 : ℝ)^4151 ≤ (8171092188047/25000000000000 : ℝ)^3127 := by
    have hnat : (86134343 : ℕ)^4151*25000000000000^3127 ≤ 8171092188047^3127*200000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86134343 200000000 8171092188047 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70290357/156250000 : ℝ), (4306717461/10000000000 : ℝ), (86134343/200000000 : ℝ)] ![(34631259349441/100000000000000 : ℝ), (16342185942661/50000000000000 : ℝ), (8171092188047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70290357/156250000 : ℝ)|^4151 ≤ (34631259349441/100000000000000 : ℝ)^3127
        have hw : |(70290357/156250000 : ℝ)|=(70290357/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4306717461/10000000000 : ℝ)|^4151 ≤ (16342185942661/50000000000000 : ℝ)^3127
        have hw : |(4306717461/10000000000 : ℝ)|=(4306717461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86134343/200000000 : ℝ)|^4151 ≤ (8171092188047/25000000000000 : ℝ)^3127
        have hw : |(86134343/200000000 : ℝ)|=(86134343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_12 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108899407/10000000000 : ℝ)*x 0 + (1360185847/2500000000 : ℝ)*x 1 + (1054537009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108899407/10000000000 : ℝ)^4151 ≤ (12667886265149/100000000000000 : ℝ)^3127 := by
    have hnat : (2108899407 : ℕ)^4151*100000000000000^3127 ≤ 12667886265149^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108899407 10000000000 12667886265149 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360185847/2500000000 : ℝ)^4151 ≤ (278595536653/625000000000 : ℝ)^3127 := by
    have hnat : (1360185847 : ℕ)^4151*625000000000^3127 ≤ 278595536653^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360185847 2500000000 278595536653 625000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054537009/2000000000 : ℝ)^4151 ≤ (4275682785447/10000000000000 : ℝ)^3127 := by
    have hnat : (1054537009 : ℕ)^4151*10000000000000^3127 ≤ 4275682785447^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054537009 2000000000 4275682785447 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108899407/10000000000 : ℝ), (1360185847/2500000000 : ℝ), (1054537009/2000000000 : ℝ)] ![(12667886265149/100000000000000 : ℝ), (278595536653/625000000000 : ℝ), (4275682785447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108899407/10000000000 : ℝ)|^4151 ≤ (12667886265149/100000000000000 : ℝ)^3127
        have hw : |(-2108899407/10000000000 : ℝ)|=(2108899407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360185847/2500000000 : ℝ)|^4151 ≤ (278595536653/625000000000 : ℝ)^3127
        have hw : |(1360185847/2500000000 : ℝ)|=(1360185847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054537009/2000000000 : ℝ)|^4151 ≤ (4275682785447/10000000000000 : ℝ)^3127
        have hw : |(1054537009/2000000000 : ℝ)|=(1054537009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_13 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369259217/10000000000 : ℝ)*x 0 + (-137842067/625000000 : ℝ)*x 1 + (5272683233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369259217/10000000000 : ℝ)^4151 ≤ (43799516598891/100000000000000 : ℝ)^3127 := by
    have hnat : (5369259217 : ℕ)^4151*100000000000000^3127 ≤ 43799516598891^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369259217 10000000000 43799516598891 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137842067/625000000 : ℝ)^4151 ≤ (6721837513481/50000000000000 : ℝ)^3127 := by
    have hnat : (137842067 : ℕ)^4151*50000000000000^3127 ≤ 6721837513481^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137842067 625000000 6721837513481 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272683233/10000000000 : ℝ)^4151 ≤ (42756808348989/100000000000000 : ℝ)^3127 := by
    have hnat : (5272683233 : ℕ)^4151*100000000000000^3127 ≤ 42756808348989^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272683233 10000000000 42756808348989 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369259217/10000000000 : ℝ), (-137842067/625000000 : ℝ), (5272683233/10000000000 : ℝ)] ![(43799516598891/100000000000000 : ℝ), (6721837513481/50000000000000 : ℝ), (42756808348989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369259217/10000000000 : ℝ)|^4151 ≤ (43799516598891/100000000000000 : ℝ)^3127
        have hw : |(5369259217/10000000000 : ℝ)|=(5369259217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137842067/625000000 : ℝ)|^4151 ≤ (6721837513481/50000000000000 : ℝ)^3127
        have hw : |(-137842067/625000000 : ℝ)|=(137842067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272683233/10000000000 : ℝ)|^4151 ≤ (42756808348989/100000000000000 : ℝ)^3127
        have hw : |(5272683233/10000000000 : ℝ)|=(5272683233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_14 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369257537/10000000000 : ℝ)*x 0 + (2636342509/5000000000 : ℝ)*x 1 + (-2205472947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369257537/10000000000 : ℝ)^4151 ≤ (4379949840653/10000000000000 : ℝ)^3127 := by
    have hnat : (5369257537 : ℕ)^4151*10000000000000^3127 ≤ 4379949840653^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369257537 10000000000 4379949840653 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636342509/5000000000 : ℝ)^4151 ≤ (1710273102553/4000000000000 : ℝ)^3127 := by
    have hnat : (2636342509 : ℕ)^4151*4000000000000^3127 ≤ 1710273102553^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636342509 5000000000 1710273102553 4000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205472947/10000000000 : ℝ)^4151 ≤ (13443674015497/100000000000000 : ℝ)^3127 := by
    have hnat : (2205472947 : ℕ)^4151*100000000000000^3127 ≤ 13443674015497^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205472947 10000000000 13443674015497 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369257537/10000000000 : ℝ), (2636342509/5000000000 : ℝ), (-2205472947/10000000000 : ℝ)] ![(4379949840653/10000000000000 : ℝ), (1710273102553/4000000000000 : ℝ), (13443674015497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369257537/10000000000 : ℝ)|^4151 ≤ (4379949840653/10000000000000 : ℝ)^3127
        have hw : |(5369257537/10000000000 : ℝ)|=(5369257537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636342509/5000000000 : ℝ)|^4151 ≤ (1710273102553/4000000000000 : ℝ)^3127
        have hw : |(2636342509/5000000000 : ℝ)|=(2636342509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205472947/10000000000 : ℝ)|^4151 ≤ (13443674015497/100000000000000 : ℝ)^3127
        have hw : |(-2205472947/10000000000 : ℝ)|=(2205472947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_box_15 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242817403/10000000000 : ℝ)*x 0 + (554324753/1250000000 : ℝ)*x 1 + (2217298411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242817403/10000000000 : ℝ)^4151 ≤ (16021093578773/50000000000000 : ℝ)^3127 := by
    have hnat : (4242817403 : ℕ)^4151*50000000000000^3127 ≤ 16021093578773^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242817403 10000000000 16021093578773 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554324753/1250000000 : ℝ)^4151 ≤ (16989456263571/50000000000000 : ℝ)^3127 := by
    have hnat : (554324753 : ℕ)^4151*50000000000000^3127 ≤ 16989456263571^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554324753 1250000000 16989456263571 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217298411/5000000000 : ℝ)^4151 ≤ (16989450150569/50000000000000 : ℝ)^3127 := by
    have hnat : (2217298411 : ℕ)^4151*50000000000000^3127 ≤ 16989450150569^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217298411 5000000000 16989450150569 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242817403/10000000000 : ℝ), (554324753/1250000000 : ℝ), (2217298411/5000000000 : ℝ)] ![(16021093578773/50000000000000 : ℝ), (16989456263571/50000000000000 : ℝ), (16989450150569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242817403/10000000000 : ℝ)|^4151 ≤ (16021093578773/50000000000000 : ℝ)^3127
        have hw : |(4242817403/10000000000 : ℝ)|=(4242817403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554324753/1250000000 : ℝ)|^4151 ≤ (16989456263571/50000000000000 : ℝ)^3127
        have hw : |(554324753/1250000000 : ℝ)|=(554324753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2217298411/5000000000 : ℝ)|^4151 ≤ (16989450150569/50000000000000 : ℝ)^3127
        have hw : |(2217298411/5000000000 : ℝ)|=(2217298411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59273/100000 : ℝ) ∧ (79707/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1661/2000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11311/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (1457567978811413/10000000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^8301 ≤ (1457567978811413/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11311 : ℕ)^8301*10000000000000000000^2048 ≤ 1457567978811413^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 1457567978811413 10000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (1457567978811413/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (4361334229487221/12500000000000000000 : ℝ) := by
    have hpowers : (14029/100000 : ℝ)^8301 ≤ (4361334229487221/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14029 : ℕ)^8301*12500000000000000000^2048 ≤ 4361334229487221^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 100000 4361334229487221 12500000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/100000 : ℝ)) (X := (4361334229487221/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001457567978811413/5000000000000000000 : ℝ) ≤ (5000359567705607/5000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (5001457567978811413/5000000000000000000 : ℝ)^2048 ≤ (5000359567705607/5000000000000000 : ℝ)^8301 := by
      have hnat : (5001457567978811413 : ℕ)^2048*5000000000000000^8301 ≤ 5000359567705607^8301*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001457567978811413 5000000000000000000 5000359567705607 5000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359567705607/5000000000000000 : ℝ)) (X := (5001457567978811413/5000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024733176812005949/50000000000000000000 : ℝ) ≤ (2000244038605171/2000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50024733176812005949/50000000000000000000 : ℝ)^2048 ≤ (2000244038605171/2000000000000000 : ℝ)^8301 := by
      have hnat : (50024733176812005949 : ℕ)^2048*2000000000000000^8301 ≤ 2000244038605171^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024733176812005949 50000000000000000000 2000244038605171 2000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000244038605171/2000000000000000 : ℝ)) (X := (50024733176812005949/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254361334229487221/6250000000000000000 : ℝ) ≤ (625107578165031/625000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (6254361334229487221/6250000000000000000 : ℝ)^2048 ≤ (625107578165031/625000000000000 : ℝ)^8301 := by
      have hnat : (6254361334229487221 : ℕ)^2048*625000000000000^8301 ≤ 625107578165031^8301*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254361334229487221 6250000000000000000 625107578165031 625000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625107578165031/625000000000000 : ℝ)) (X := (6254361334229487221/6250000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1457567978811413/10000000000000000000 : ℝ) ≤ ((543412393693785419/543600000000000000 : ℝ)+2*(501057614641/271800000000000 : ℝ)*(11311/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (543412393693785419/543600000000000000 : ℝ)+2*(501057614641/271800000000000 : ℝ)*(11311/100000 : ℝ)=(5000359567705607/5000000000000000 : ℝ) by norm_num, show 1+2*(1457567978811413/10000000000000000000 : ℝ)=(5001457567978811413/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4361334229487221/12500000000000000000 : ℝ)+(1457567978811413/10000000000000000000 : ℝ) ≤ ((543412393693785419/543600000000000000 : ℝ)+(501057614641/271800000000000 : ℝ)*((14029/100000 : ℝ)+(11311/100000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (543412393693785419/543600000000000000 : ℝ)+(501057614641/271800000000000 : ℝ)*((14029/100000 : ℝ)+(11311/100000 : ℝ))=(2000244038605171/2000000000000000 : ℝ) by norm_num, show 1+(4361334229487221/12500000000000000000 : ℝ)+(1457567978811413/10000000000000000000 : ℝ)=(50024733176812005949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4361334229487221/12500000000000000000 : ℝ) ≤ ((543412393693785419/543600000000000000 : ℝ)+2*(501057614641/271800000000000 : ℝ)*(14029/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (543412393693785419/543600000000000000 : ℝ)+2*(501057614641/271800000000000 : ℝ)*(14029/100000 : ℝ)=(625107578165031/625000000000000 : ℝ) by norm_num, show 1+2*(4361334229487221/12500000000000000000 : ℝ)=(6254361334229487221/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (543412393693785419/543600000000000000 : ℝ)*(X 1 0+X 2 0)+(501057614641/271800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (543412393693785419/543600000000000000 : ℝ)) (alpha := (501057614641/271800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (543412393693785419/543600000000000000 : ℝ)*(X 0 1+X 2 1)+(501057614641/271800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (543412393693785419/543600000000000000 : ℝ)) (alpha := (501057614641/271800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (543412393693785419/543600000000000000 : ℝ)*(X 0 2+X 1 2)+(501057614641/271800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (543412393693785419/543600000000000000 : ℝ)) (alpha := (501057614641/271800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-513694817/2500000000 : ℝ)*X 0 0+(5376774889/10000000000 : ℝ)*X 0 1+(5376774801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323916429/2500000000 : ℝ)*X 1 0+(-17317543/80000000 : ℝ)*X 1 1+(1344193739/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295665849/10000000000 : ℝ)*X 2 0+(5376774703/10000000000 : ℝ)*X 2 1+(-2164693039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2238622303/5000000000 : ℝ)*X 0 0+(4317526703/10000000000 : ℝ)*X 0 1+(539690899/1250000000 : ℝ)*X 0 2+(2238622303/5000000000 : ℝ)*X 1 0+(4317526703/10000000000 : ℝ)*X 1 1+(539690899/1250000000 : ℝ)*X 1 2+(2238622303/5000000000 : ℝ)*X 2 0+(4317526703/10000000000 : ℝ)*X 2 1+(539690899/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1156071847/5000000000 : ℝ)*X 0 0+(5280708177/10000000000 : ℝ)*X 0 1+(2640353263/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((670448451/1250000000 : ℝ)*X 1 0+(-1101191671/5000000000 : ℝ)*X 1 1+(211228307/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((670448469/1250000000 : ℝ)*X 2 0+(5280707499/10000000000 : ℝ)*X 2 1+(-275297923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266318673/625000000 : ℝ)*X 0 0+(4425578879/10000000000 : ℝ)*X 0 1+(4425578651/10000000000 : ℝ)*X 0 2+(266318673/625000000 : ℝ)*X 1 0+(4425578879/10000000000 : ℝ)*X 1 1+(4425578651/10000000000 : ℝ)*X 1 2+(266318673/625000000 : ℝ)*X 2 0+(4425578879/10000000000 : ℝ)*X 2 1+(4425578651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2258363771/10000000000 : ℝ)*X 0 0+(2607717931/5000000000 : ℝ)*X 0 1+(1346595117/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288871257/10000000000 : ℝ)*X 1 0+(-2160853573/10000000000 : ℝ)*X 1 1+(1346595181/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288870939/10000000000 : ℝ)*X 2 0+(269318997/500000000 : ℝ)*X 2 1+(-135053441/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((70290357/156250000 : ℝ)*X 0 0+(4306717461/10000000000 : ℝ)*X 0 1+(86134343/200000000 : ℝ)*X 0 2+(70290357/156250000 : ℝ)*X 1 0+(4306717461/10000000000 : ℝ)*X 1 1+(86134343/200000000 : ℝ)*X 1 2+(70290357/156250000 : ℝ)*X 2 0+(4306717461/10000000000 : ℝ)*X 2 1+(86134343/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2108899407/10000000000 : ℝ)*X 0 0+(1360185847/2500000000 : ℝ)*X 0 1+(1054537009/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369259217/10000000000 : ℝ)*X 1 0+(-137842067/625000000 : ℝ)*X 1 1+(5272683233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369257537/10000000000 : ℝ)*X 2 0+(2636342509/5000000000 : ℝ)*X 2 1+(-2205472947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4242817403/10000000000 : ℝ)*X 0 0+(554324753/1250000000 : ℝ)*X 0 1+(2217298411/5000000000 : ℝ)*X 0 2+(4242817403/10000000000 : ℝ)*X 1 0+(554324753/1250000000 : ℝ)*X 1 1+(2217298411/5000000000 : ℝ)*X 1 2+(4242817403/10000000000 : ℝ)*X 2 0+(554324753/1250000000 : ℝ)*X 2 1+(2217298411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-704699230951774733148004674391/1132500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86803693/100000000000000 : ℝ)*(upper0) + (83138577/50000000000000 : ℝ)*(upper1) + (62984659/100000000000000 : ℝ)*(upper3) + (50870031/50000000000000 : ℝ)*(upper5) + (973253301883489/25000000000000 : ℝ)*(major0) + (973253301883489/25000000000000 : ℝ)*(major1) + (973253301883489/25000000000000 : ℝ)*(major2) + (1838068189/12500000000000 : ℝ)*(sp3) + (207638851904583/4000000000000 : ℝ)*(sp4) + (2595447854112103/50000000000000 : ℝ)*(sp5) + (1297756876610551/25000000000000 : ℝ)*(sp6) + (326965737912347/12500000000000 : ℝ)*(sp7) + (5620882763/10000000000000 : ℝ)*(sp8) + (65899108999/50000000000000 : ℝ)*(sp13) + (40870946997567/1562500000000 : ℝ)*(f.failure) + (1297756876610551/25000000000000 : ℝ)*(f.sum) + (8954070007099/3397500000000000000000000000 : ℝ)*base65 + (52651615811305109/13590000000000000000000000000000 : ℝ)*base68 + (215444634965644891/13590000000000000000000000000000 : ℝ)*base69 + (92686133926084891/13590000000000000000000000000000 : ℝ)*base71 + (59467592855479/3397500000000000000000000000 : ℝ)*base73 + (178310485980184891/13590000000000000000000000000000 : ℝ)*base75 + (71672479633624891/13590000000000000000000000000000 : ℝ)*base77 + (515443802528704891/13590000000000000000000000000000 : ℝ)*base79 + (368004210709/3397500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1240951/156250000000000000000 : ℝ)*base90 + (1240951/156250000000000000000 : ℝ)*base92 + (1240951/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59273/100000 : ℝ) ≤ (447531361203223740122718754281/755000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29680761/50000000000000 : ℝ)*(upper0) + (18672239/20000000000000 : ℝ)*(upper2) + (9225903/50000000000000 : ℝ)*(upper4) + (32883901/50000000000000 : ℝ)*(upper5) + (1978300459670103/50000000000000 : ℝ)*(major0) + (1978300459670103/50000000000000 : ℝ)*(major1) + (1978300459670103/50000000000000 : ℝ)*(major2) + (2617488261147651/50000000000000 : ℝ)*(sp0) + (2617483989639993/50000000000000 : ℝ)*(sp1) + (2617430965748501/50000000000000 : ℝ)*(sp2) + (1329232800151237/50000000000000 : ℝ)*(sp3) + (9700104417/100000000000000 : ℝ)*(sp5) + (115747887401/100000000000000 : ℝ)*(sp10) + (1157089101/100000000000000 : ℝ)*(sp12) + (1329232800151237/50000000000000 : ℝ)*(f.failure) + (1308744419846101/25000000000000 : ℝ)*(f.sum) + (1006691429923/188750000000000000000000000 : ℝ)*base65 + (19852695912018427/3020000000000000000000000000000 : ℝ)*base68 + (40635477315641573/3020000000000000000000000000000 : ℝ)*base69 + (4040846866621573/3020000000000000000000000000000 : ℝ)*base71 + (4255394516343/755000000000000000000000000 : ℝ)*base74 + (23298709350761573/3020000000000000000000000000000 : ℝ)*base75 + (6523287697121573/3020000000000000000000000000000 : ℝ)*base77 + (12249328234381573/3020000000000000000000000000000 : ℝ)*base79 + (4287194458577/755000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (59934461/5000000000000000000000 : ℝ)*base90 + (59934461/5000000000000000000000 : ℝ)*base92 + (59934461/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79707/100000 : ℝ) ≤ (601803671184884186365570520937/755000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60554547/100000000000000 : ℝ)*(upper0) + (49647129/50000000000000 : ℝ)*(upper1) + (117244517/20000000000000 : ℝ)*(upper2) + (43443621/6250000000000 : ℝ)*(lower5) + (2212345337267831/50000000000000 : ℝ)*(major0) + (2212345337267831/50000000000000 : ℝ)*(major1) + (2212345337267831/50000000000000 : ℝ)*(major2) + (29450312221/5000000000000 : ℝ)*(sp1) + (93753493133/50000000000000 : ℝ)*(sp3) + (1873307949/6250000000000 : ℝ)*(sp4) + (5849803560805979/100000000000000 : ℝ)*(sp8) + (731155565936093/12500000000000 : ℝ)*(sp9) + (1462458383433291/25000000000000 : ℝ)*(sp10) + (118911624393793/4000000000000 : ℝ)*(sp11) + (743244529207773/25000000000000 : ℝ)*(f.failure) + (1462458383433291/25000000000000 : ℝ)*(f.sum) + (16373687786837/3397500000000000000000000000 : ℝ)*base66 + (285152488467878189/27180000000000000000000000000000 : ℝ)*base67 + (258503531606858189/27180000000000000000000000000000 : ℝ)*base69 + (194267299554578189/27180000000000000000000000000000 : ℝ)*base71 + (2467208870713/3397500000000000000000000000 : ℝ)*base73 + (139332951527258189/27180000000000000000000000000000 : ℝ)*base75 + (18203790593661811/27180000000000000000000000000000 : ℝ)*base78 + (605677321744958189/27180000000000000000000000000000 : ℝ)*base79 + (15059571641539/6795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19909931/2500000000000000000000 : ℝ)*base89 + (19909931/2500000000000000000000 : ℝ)*base91 + (19909931/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-1661/2000 : ℝ) ≤ (-2076191643637016126425215619/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45586527/25000000000000 : ℝ)*(lower0) + (155817751/50000000000000 : ℝ)*(upper1) + (125569099/100000000000000 : ℝ)*(upper3) + (386928741/100000000000000 : ℝ)*(lower4) + (1114872815392647/25000000000000 : ℝ)*(major0) + (1114872815392647/25000000000000 : ℝ)*(major1) + (1114872815392647/25000000000000 : ℝ)*(major2) + (1111764185199/100000000000000 : ℝ)*(sp5) + (15720884271/50000000000000 : ℝ)*(sp6) + (246870256959/100000000000000 : ℝ)*(sp7) + (1487576055836871/25000000000000 : ℝ)*(sp12) + (1189838491832457/20000000000000 : ℝ)*(sp13) + (2975136390789471/50000000000000 : ℝ)*(sp14) + (149805699239261/5000000000000 : ℝ)*(sp15) + (149818042752109/5000000000000 : ℝ)*(f.failure) + (1487576055836871/25000000000000 : ℝ)*(f.sum) + (21982144679/7500000000000000000000000 : ℝ)*base65 + (19880513883881/30000000000000000000000000000 : ℝ)*base67 + (31945082996119/30000000000000000000000000000 : ℝ)*base70 + (50350835396119/30000000000000000000000000000 : ℝ)*base72 + (12545867173/15000000000000000000000000 : ℝ)*base73 + (4974871496119/30000000000000000000000000000 : ℝ)*base76 + (223619993426119/30000000000000000000000000000 : ℝ)*base78 + (479018034776119/30000000000000000000000000000 : ℝ)*base80 + (153620337913/15000000000000000000000000 : ℝ)*base81 + (2240923/500000000000000000000 : ℝ)*base89 + (2240923/500000000000000000000 : ℝ)*base91 + (2240923/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1109_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59273/100000 : ℝ) else (79707/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1661/2000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1109_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1109_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59273/100000 : ℝ) else (79707/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1661/2000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1109_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1109_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59273/100000 : ℝ) else (79707/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1661/2000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

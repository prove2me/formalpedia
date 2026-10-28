-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1035_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:42:34.402511+00:00
-- url     : https://prove2.me/submissions/d3123554-cbfd-4350-a3f9-aef331adfd55

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
theorem support_rectangle_w1035_s3_0 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-138371807/625000000 : ℝ)*x 0 + (5441193879/10000000000 : ℝ)*x 1 + (652618921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138371807/625000000 : ℝ)^2057 ≤ (839540522671/6250000000000 : ℝ)^1545 := by
    have hnat : (138371807 : ℕ)^2057*6250000000000^1545 ≤ 839540522671^1545*625000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138371807 625000000 839540522671 6250000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441193879/10000000000 : ℝ)^2057 ≤ (11118481853511/25000000000000 : ℝ)^1545 := by
    have hnat : (5441193879 : ℕ)^2057*25000000000000^1545 ≤ 11118481853511^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441193879 10000000000 11118481853511 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652618921/1250000000 : ℝ)^2057 ≤ (4209342420887/10000000000000 : ℝ)^1545 := by
    have hnat : (652618921 : ℕ)^2057*10000000000000^1545 ≤ 4209342420887^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652618921 1250000000 4209342420887 10000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138371807/625000000 : ℝ), (5441193879/10000000000 : ℝ), (652618921/1250000000 : ℝ)] ![(839540522671/6250000000000 : ℝ), (11118481853511/25000000000000 : ℝ), (4209342420887/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138371807/625000000 : ℝ)|^2057 ≤ (839540522671/6250000000000 : ℝ)^1545
        have hw : |(-138371807/625000000 : ℝ)|=(138371807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441193879/10000000000 : ℝ)|^2057 ≤ (11118481853511/25000000000000 : ℝ)^1545
        have hw : |(5441193879/10000000000 : ℝ)|=(5441193879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652618921/1250000000 : ℝ)|^2057 ≤ (4209342420887/10000000000000 : ℝ)^1545
        have hw : |(652618921/1250000000 : ℝ)|=(652618921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_1 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5356490097/10000000000 : ℝ)*x 0 + (-232681917/1000000000 : ℝ)*x 1 + (326309487/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356490097/10000000000 : ℝ)^2057 ≤ (10888637251599/25000000000000 : ℝ)^1545 := by
    have hnat : (5356490097 : ℕ)^2057*25000000000000^1545 ≤ 10888637251599^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356490097 10000000000 10888637251599 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232681917/1000000000 : ℝ)^2057 ≤ (1794002777217/12500000000000 : ℝ)^1545 := by
    have hnat : (232681917 : ℕ)^2057*12500000000000^1545 ≤ 1794002777217^1545*1000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232681917 1000000000 1794002777217 12500000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326309487/625000000 : ℝ)^2057 ≤ (21046714380089/50000000000000 : ℝ)^1545 := by
    have hnat : (326309487 : ℕ)^2057*50000000000000^1545 ≤ 21046714380089^1545*625000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326309487 625000000 21046714380089 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356490097/10000000000 : ℝ), (-232681917/1000000000 : ℝ), (326309487/625000000 : ℝ)] ![(10888637251599/25000000000000 : ℝ), (1794002777217/12500000000000 : ℝ), (21046714380089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356490097/10000000000 : ℝ)|^2057 ≤ (10888637251599/25000000000000 : ℝ)^1545
        have hw : |(5356490097/10000000000 : ℝ)|=(5356490097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232681917/1000000000 : ℝ)|^2057 ≤ (1794002777217/12500000000000 : ℝ)^1545
        have hw : |(-232681917/1000000000 : ℝ)|=(232681917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326309487/625000000 : ℝ)|^2057 ≤ (21046714380089/50000000000000 : ℝ)^1545
        have hw : |(326309487/625000000 : ℝ)|=(326309487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_2 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5356490321/10000000000 : ℝ)*x 0 + (5220951709/10000000000 : ℝ)*x 1 + (-1163409491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356490321/10000000000 : ℝ)^2057 ≤ (4355455143137/10000000000000 : ℝ)^1545 := by
    have hnat : (5356490321 : ℕ)^2057*10000000000000^1545 ≤ 4355455143137^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356490321 10000000000 4355455143137 10000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220951709/10000000000 : ℝ)^2057 ≤ (21046713934619/50000000000000 : ℝ)^1545 := by
    have hnat : (5220951709 : ℕ)^2057*50000000000000^1545 ≤ 21046713934619^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220951709 10000000000 21046713934619 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1163409491/5000000000 : ℝ)^2057 ≤ (7176010336927/50000000000000 : ℝ)^1545 := by
    have hnat : (1163409491 : ℕ)^2057*50000000000000^1545 ≤ 7176010336927^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163409491 5000000000 7176010336927 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356490321/10000000000 : ℝ), (5220951709/10000000000 : ℝ), (-1163409491/5000000000 : ℝ)] ![(4355455143137/10000000000000 : ℝ), (21046713934619/50000000000000 : ℝ), (7176010336927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356490321/10000000000 : ℝ)|^2057 ≤ (4355455143137/10000000000000 : ℝ)^1545
        have hw : |(5356490321/10000000000 : ℝ)|=(5356490321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220951709/10000000000 : ℝ)|^2057 ≤ (21046713934619/50000000000000 : ℝ)^1545
        have hw : |(5220951709/10000000000 : ℝ)|=(5220951709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1163409491/5000000000 : ℝ)|^2057 ≤ (7176010336927/50000000000000 : ℝ)^1545
        have hw : |(-1163409491/5000000000 : ℝ)|=(1163409491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_3 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1094228589/2500000000 : ℝ)*x 0 + (4167775771/10000000000 : ℝ)*x 1 + (2298381703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094228589/2500000000 : ℝ)^2057 ≤ (33285429052573/100000000000000 : ℝ)^1545 := by
    have hnat : (1094228589 : ℕ)^2057*100000000000000^1545 ≤ 33285429052573^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094228589 2500000000 33285429052573 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4167775771/10000000000 : ℝ)^2057 ≤ (15592431624917/50000000000000 : ℝ)^1545 := by
    have hnat : (4167775771 : ℕ)^2057*50000000000000^1545 ≤ 15592431624917^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167775771 10000000000 15592431624917 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2298381703/5000000000 : ℝ)^2057 ≤ (35529707690161/100000000000000 : ℝ)^1545 := by
    have hnat : (2298381703 : ℕ)^2057*100000000000000^1545 ≤ 35529707690161^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298381703 5000000000 35529707690161 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094228589/2500000000 : ℝ), (4167775771/10000000000 : ℝ), (2298381703/5000000000 : ℝ)] ![(33285429052573/100000000000000 : ℝ), (15592431624917/50000000000000 : ℝ), (35529707690161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094228589/2500000000 : ℝ)|^2057 ≤ (33285429052573/100000000000000 : ℝ)^1545
        have hw : |(1094228589/2500000000 : ℝ)|=(1094228589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4167775771/10000000000 : ℝ)|^2057 ≤ (15592431624917/50000000000000 : ℝ)^1545
        have hw : |(4167775771/10000000000 : ℝ)|=(4167775771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2298381703/5000000000 : ℝ)|^2057 ≤ (35529707690161/100000000000000 : ℝ)^1545
        have hw : |(2298381703/5000000000 : ℝ)|=(2298381703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_4 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213973887/10000000000 : ℝ)*x 0 + (1044375089/2000000000 : ℝ)*x 1 + (170008243/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213973887/10000000000 : ℝ)^2057 ≤ (1343285010931/10000000000000 : ℝ)^1545 := by
    have hnat : (2213973887 : ℕ)^2057*10000000000000^1545 ≤ 1343285010931^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213973887 10000000000 1343285010931 10000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044375089/2000000000 : ℝ)^2057 ≤ (10525835935961/25000000000000 : ℝ)^1545 := by
    have hnat : (1044375089 : ℕ)^2057*25000000000000^1545 ≤ 10525835935961^1545*2000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044375089 2000000000 10525835935961 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170008243/312500000 : ℝ)^2057 ≤ (44463806124857/100000000000000 : ℝ)^1545 := by
    have hnat : (170008243 : ℕ)^2057*100000000000000^1545 ≤ 44463806124857^1545*312500000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170008243 312500000 44463806124857 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213973887/10000000000 : ℝ), (1044375089/2000000000 : ℝ), (170008243/312500000 : ℝ)] ![(1343285010931/10000000000000 : ℝ), (10525835935961/25000000000000 : ℝ), (44463806124857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213973887/10000000000 : ℝ)|^2057 ≤ (1343285010931/10000000000000 : ℝ)^1545
        have hw : |(-2213973887/10000000000 : ℝ)|=(2213973887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044375089/2000000000 : ℝ)|^2057 ≤ (10525835935961/25000000000000 : ℝ)^1545
        have hw : |(1044375089/2000000000 : ℝ)|=(1044375089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170008243/312500000 : ℝ)|^2057 ≤ (44463806124857/100000000000000 : ℝ)^1545
        have hw : |(170008243/312500000 : ℝ)|=(170008243/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_5 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662643411/1250000000 : ℝ)*x 0 + (-2107506743/10000000000 : ℝ)*x 1 + (27201321/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662643411/1250000000 : ℝ)^2057 ≤ (42956448225961/100000000000000 : ℝ)^1545 := by
    have hnat : (662643411 : ℕ)^2057*100000000000000^1545 ≤ 42956448225961^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662643411 1250000000 42956448225961 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107506743/10000000000 : ℝ)^2057 ≤ (2515948204267/20000000000000 : ℝ)^1545 := by
    have hnat : (2107506743 : ℕ)^2057*20000000000000^1545 ≤ 2515948204267^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107506743 10000000000 2515948204267 20000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27201321/50000000 : ℝ)^2057 ≤ (44463810738653/100000000000000 : ℝ)^1545 := by
    have hnat : (27201321 : ℕ)^2057*100000000000000^1545 ≤ 44463810738653^1545*50000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27201321 50000000 44463810738653 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662643411/1250000000 : ℝ), (-2107506743/10000000000 : ℝ), (27201321/50000000 : ℝ)] ![(42956448225961/100000000000000 : ℝ), (2515948204267/20000000000000 : ℝ), (44463810738653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662643411/1250000000 : ℝ)|^2057 ≤ (42956448225961/100000000000000 : ℝ)^1545
        have hw : |(662643411/1250000000 : ℝ)|=(662643411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107506743/10000000000 : ℝ)|^2057 ≤ (2515948204267/20000000000000 : ℝ)^1545
        have hw : |(-2107506743/10000000000 : ℝ)|=(2107506743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27201321/50000000 : ℝ)|^2057 ≤ (44463810738653/100000000000000 : ℝ)^1545
        have hw : |(27201321/50000000 : ℝ)|=(27201321/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_6 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650573583/5000000000 : ℝ)*x 0 + (680033/1250000 : ℝ)*x 1 + (-2107507183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650573583/5000000000 : ℝ)^2057 ≤ (21478223454877/50000000000000 : ℝ)^1545 := by
    have hnat : (2650573583 : ℕ)^2057*50000000000000^1545 ≤ 21478223454877^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650573583 5000000000 21478223454877 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680033/1250000 : ℝ)^2057 ≤ (22231904281167/50000000000000 : ℝ)^1545 := by
    have hnat : (680033 : ℕ)^2057*50000000000000^1545 ≤ 22231904281167^1545*1250000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680033 1250000 22231904281167 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107507183/10000000000 : ℝ)^2057 ≤ (6289872259029/50000000000000 : ℝ)^1545 := by
    have hnat : (2107507183 : ℕ)^2057*50000000000000^1545 ≤ 6289872259029^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107507183 10000000000 6289872259029 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650573583/5000000000 : ℝ), (680033/1250000 : ℝ), (-2107507183/10000000000 : ℝ)] ![(21478223454877/50000000000000 : ℝ), (22231904281167/50000000000000 : ℝ), (6289872259029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650573583/5000000000 : ℝ)|^2057 ≤ (21478223454877/50000000000000 : ℝ)^1545
        have hw : |(2650573583/5000000000 : ℝ)|=(2650573583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680033/1250000 : ℝ)|^2057 ≤ (22231904281167/50000000000000 : ℝ)^1545
        have hw : |(680033/1250000 : ℝ)|=(680033/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107507183/10000000000 : ℝ)|^2057 ≤ (6289872259029/50000000000000 : ℝ)^1545
        have hw : |(-2107507183/10000000000 : ℝ)|=(2107507183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s3_7 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4376961799/10000000000 : ℝ)*x 0 + (574370617/1250000000 : ℝ)*x 1 + (4169585119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376961799/10000000000 : ℝ)^2057 ≤ (33285909410367/100000000000000 : ℝ)^1545 := by
    have hnat : (4376961799 : ℕ)^2057*100000000000000^1545 ≤ 33285909410367^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376961799 10000000000 33285909410367 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574370617/1250000000 : ℝ)^2057 ≤ (17755600679463/50000000000000 : ℝ)^1545 := by
    have hnat : (574370617 : ℕ)^2057*50000000000000^1545 ≤ 17755600679463^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574370617 1250000000 17755600679463 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169585119/10000000000 : ℝ)^2057 ≤ (31202889219961/100000000000000 : ℝ)^1545 := by
    have hnat : (4169585119 : ℕ)^2057*100000000000000^1545 ≤ 31202889219961^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169585119 10000000000 31202889219961 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376961799/10000000000 : ℝ), (574370617/1250000000 : ℝ), (4169585119/10000000000 : ℝ)] ![(33285909410367/100000000000000 : ℝ), (17755600679463/50000000000000 : ℝ), (31202889219961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376961799/10000000000 : ℝ)|^2057 ≤ (33285909410367/100000000000000 : ℝ)^1545
        have hw : |(4376961799/10000000000 : ℝ)|=(4376961799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574370617/1250000000 : ℝ)|^2057 ≤ (17755600679463/50000000000000 : ℝ)^1545
        have hw : |(574370617/1250000000 : ℝ)|=(574370617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169585119/10000000000 : ℝ)|^2057 ≤ (31202889219961/100000000000000 : ℝ)^1545
        have hw : |(4169585119/10000000000 : ℝ)|=(4169585119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1035_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (107/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (2573/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14951/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (107/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (107/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (107/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (107/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (107/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (107/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (107/1250 : ℝ) ^ (8227/2048 : ℝ) ≤ (205926004661869/4000000000000000000 : ℝ) := by
    have hpowers : (107/1250 : ℝ)^8227 ≤ (205926004661869/4000000000000000000 : ℝ)^2048 := by
      have hnat : (107 : ℕ)^8227*4000000000000000000^2048 ≤ 205926004661869^2048*1250^8227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107 1250 205926004661869 4000000000000000000 8227 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (107/1250 : ℝ)) (X := (205926004661869/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8421/50000 : ℝ) ^ (8227/2048 : ℝ) ≤ (39023286730357677/50000000000000000000 : ℝ) := by
    have hpowers : (8421/50000 : ℝ)^8227 ≤ (39023286730357677/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8421 : ℕ)^8227*50000000000000000000^2048 ≤ 39023286730357677^2048*50000^8227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8421 50000 39023286730357677 50000000000000000000 8227 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8421/50000 : ℝ)) (X := (39023286730357677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000205926004661869/2000000000000000000 : ℝ) ≤ (10000256302511071/10000000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (2000205926004661869/2000000000000000000 : ℝ)^2048 ≤ (10000256302511071/10000000000000000 : ℝ)^8227 := by
      have hnat : (2000205926004661869 : ℕ)^2048*10000000000000000^8227 ≤ 10000256302511071^8227*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000205926004661869 2000000000000000000 10000256302511071 10000000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000256302511071/10000000000000000 : ℝ)) (X := (2000205926004661869/2000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100083194723577262079/100000000000000000000 : ℝ) ≤ (10002070373019081/10000000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (100083194723577262079/100000000000000000000 : ℝ)^2048 ≤ (10002070373019081/10000000000000000 : ℝ)^8227 := by
      have hnat : (100083194723577262079 : ℕ)^2048*10000000000000000^8227 ≤ 10002070373019081^8227*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083194723577262079 100000000000000000000 10002070373019081 10000000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002070373019081/10000000000000000 : ℝ)) (X := (100083194723577262079/100000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25039023286730357677/25000000000000000000 : ℝ) ≤ (10003884443527091/10000000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (25039023286730357677/25000000000000000000 : ℝ)^2048 ≤ (10003884443527091/10000000000000000 : ℝ)^8227 := by
      have hnat : (25039023286730357677 : ℕ)^2048*10000000000000000^8227 ≤ 10003884443527091^8227*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039023286730357677 25000000000000000000 10003884443527091 10000000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003884443527091/10000000000000000 : ℝ)) (X := (25039023286730357677/25000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(205926004661869/4000000000000000000 : ℝ) ≤ ((41395532905149779411/41410000000000000000 : ℝ)+2*(181407050801/82820000000000 : ℝ)*(107/1250 : ℝ))^(8227/2048 : ℝ) := by
    rw [show (41395532905149779411/41410000000000000000 : ℝ)+2*(181407050801/82820000000000 : ℝ)*(107/1250 : ℝ)=(10000256302511071/10000000000000000 : ℝ) by norm_num, show 1+2*(205926004661869/4000000000000000000 : ℝ)=(2000205926004661869/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39023286730357677/50000000000000000000 : ℝ)+(205926004661869/4000000000000000000 : ℝ) ≤ ((41395532905149779411/41410000000000000000 : ℝ)+(181407050801/82820000000000 : ℝ)*((8421/50000 : ℝ)+(107/1250 : ℝ)))^(8227/2048 : ℝ) := by
    rw [show (41395532905149779411/41410000000000000000 : ℝ)+(181407050801/82820000000000 : ℝ)*((8421/50000 : ℝ)+(107/1250 : ℝ))=(10002070373019081/10000000000000000 : ℝ) by norm_num, show 1+(39023286730357677/50000000000000000000 : ℝ)+(205926004661869/4000000000000000000 : ℝ)=(100083194723577262079/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39023286730357677/50000000000000000000 : ℝ) ≤ ((41395532905149779411/41410000000000000000 : ℝ)+2*(181407050801/82820000000000 : ℝ)*(8421/50000 : ℝ))^(8227/2048 : ℝ) := by
    rw [show (41395532905149779411/41410000000000000000 : ℝ)+2*(181407050801/82820000000000 : ℝ)*(8421/50000 : ℝ)=(10003884443527091/10000000000000000 : ℝ) by norm_num, show 1+2*(39023286730357677/50000000000000000000 : ℝ)=(25039023286730357677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41395532905149779411/41410000000000000000 : ℝ)*(X 1 0+X 2 0)+(181407050801/82820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (107/1250 : ℝ)) (hi := (8421/50000 : ℝ)) (c := (41395532905149779411/41410000000000000000 : ℝ)) (alpha := (181407050801/82820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41395532905149779411/41410000000000000000 : ℝ)*(X 0 1+X 2 1)+(181407050801/82820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (107/1250 : ℝ)) (hi := (8421/50000 : ℝ)) (c := (41395532905149779411/41410000000000000000 : ℝ)) (alpha := (181407050801/82820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41395532905149779411/41410000000000000000 : ℝ)*(X 0 2+X 1 2)+(181407050801/82820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (107/1250 : ℝ)) (hi := (8421/50000 : ℝ)) (c := (41395532905149779411/41410000000000000000 : ℝ)) (alpha := (181407050801/82820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-138371807/625000000 : ℝ)*X 0 0+(5441193879/10000000000 : ℝ)*X 0 1+(652618921/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356490097/10000000000 : ℝ)*X 1 0+(-232681917/1000000000 : ℝ)*X 1 1+(326309487/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356490321/10000000000 : ℝ)*X 2 0+(5220951709/10000000000 : ℝ)*X 2 1+(-1163409491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094228589/2500000000 : ℝ)*X 0 0+(4167775771/10000000000 : ℝ)*X 0 1+(2298381703/5000000000 : ℝ)*X 0 2+(1094228589/2500000000 : ℝ)*X 1 0+(4167775771/10000000000 : ℝ)*X 1 1+(2298381703/5000000000 : ℝ)*X 1 2+(1094228589/2500000000 : ℝ)*X 2 0+(4167775771/10000000000 : ℝ)*X 2 1+(2298381703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2213973887/10000000000 : ℝ)*X 0 0+(1044375089/2000000000 : ℝ)*X 0 1+(170008243/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662643411/1250000000 : ℝ)*X 1 0+(-2107506743/10000000000 : ℝ)*X 1 1+(27201321/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650573583/5000000000 : ℝ)*X 2 0+(680033/1250000 : ℝ)*X 2 1+(-2107507183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376961799/10000000000 : ℝ)*X 0 0+(574370617/1250000000 : ℝ)*X 0 1+(4169585119/10000000000 : ℝ)*X 0 2+(4376961799/10000000000 : ℝ)*X 1 0+(574370617/1250000000 : ℝ)*X 1 1+(4169585119/10000000000 : ℝ)*X 1 2+(4376961799/10000000000 : ℝ)*X 2 0+(574370617/1250000000 : ℝ)*X 2 1+(4169585119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3700530055001913522085134921/1035250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (884822603/100000000000000 : ℝ)*(base19) + (85140319/12500000000000 : ℝ)*(base23) + (45560229/20000000000000 : ℝ)*(lower2) + (16982157/100000000000000 : ℝ)*(lower4) + (86422981/100000000000000 : ℝ)*(lower5) + (3435794015909137/100000000000000 : ℝ)*(major0) + (3435794015909137/100000000000000 : ℝ)*(major1) + (3435794015909137/100000000000000 : ℝ)*(major2) + (908095024152603/20000000000000 : ℝ)*(sp0) + (227025114768991/5000000000000 : ℝ)*(sp1) + (70945351548123/1562500000000 : ℝ)*(sp2) + (1165537818870661/50000000000000 : ℝ)*(sp3) + (28059439409/100000000000000 : ℝ)*(sp4) + (9094723589/100000000000000 : ℝ)*(sp7) + (233108473246491/10000000000000 : ℝ)*(f.failure) + (4540503180202423/100000000000000 : ℝ)*(f.sum) + (24451905366757/4141000000000000000000000000 : ℝ)*base65 + (8377393937058121693/4141000000000000000000000000000000 : ℝ)*base68 + (29859891412969121693/4141000000000000000000000000000000 : ℝ)*base70 + (13938160744865121693/4141000000000000000000000000000000 : ℝ)*base72 + (10714376446331/4141000000000000000000000000 : ℝ)*base73 + (7217046426545121693/4141000000000000000000000000000000 : ℝ)*base76 + (22957004798682878307/4141000000000000000000000000000000 : ℝ)*base77 + (30307732641236121693/4141000000000000000000000000000000 : ℝ)*base80 + (3785248122221/2070500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5498677/1000000000000000000000 : ℝ)*base90 + (5498677/1000000000000000000000 : ℝ)*base92 + (5498677/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48138826040864850733734903/12625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111016297/10000000000000 : ℝ)*(base19) + (12775651/1250000000000 : ℝ)*(base23) + (8626229/25000000000000 : ℝ)*(upper2) + (47106449/25000000000000 : ℝ)*(upper3) + (1732459249592369/50000000000000 : ℝ)*(major0) + (1732459249592369/50000000000000 : ℝ)*(major1) + (1732459249592369/50000000000000 : ℝ)*(major2) + (466848597/2000000000000 : ℝ)*(sp1) + (2345219049/12500000000000 : ℝ)*(sp2) + (1471060097/100000000000000 : ℝ)*(sp3) + (915798407471709/20000000000000 : ℝ)*(sp4) + (183158703390629/4000000000000 : ℝ)*(sp5) + (4578972253554073/100000000000000 : ℝ)*(sp6) + (73463855089113/3125000000000 : ℝ)*(sp7) + (1175422416955857/50000000000000 : ℝ)*(f.failure) + (915798407471709/20000000000000 : ℝ)*(f.sum) + (23504997773697/4141000000000000000000000000 : ℝ)*base65 + (9862359675699414659/2070500000000000000000000000000000 : ℝ)*base67 + (21489863807080414659/2070500000000000000000000000000000 : ℝ)*base69 + (3758000283299585341/2070500000000000000000000000000000 : ℝ)*base72 + (1261299633863/414100000000000000000000000 : ℝ)*base73 + (15260204942340414659/2070500000000000000000000000000000 : ℝ)*base75 + (5316989414850414659/2070500000000000000000000000000000 : ℝ)*base77 + (6868246060287914659/2070500000000000000000000000000000 : ℝ)*base79 + (3847915389627/828200000000000000000000000 : ℝ)*base81 + (48647521/5000000000000000000000 : ℝ)*base89 + (48647521/5000000000000000000000 : ℝ)*base91 + (48647521/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1035_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (107/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2573/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1035_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1035_s4_0 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108968777/5000000000 : ℝ)*x 0 + (1351891607/2500000000 : ℝ)*x 1 + (5251974467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108968777/5000000000 : ℝ)^2057 ≤ (673243896557/5000000000000 : ℝ)^1545 := by
    have hnat : (1108968777 : ℕ)^2057*5000000000000^1545 ≤ 673243896557^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108968777 5000000000 673243896557 5000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351891607/2500000000 : ℝ)^2057 ≤ (44108361691751/100000000000000 : ℝ)^1545 := by
    have hnat : (1351891607 : ℕ)^2057*100000000000000^1545 ≤ 44108361691751^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351891607 2500000000 44108361691751 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5251974467/10000000000 : ℝ)^2057 ≤ (42426760358043/100000000000000 : ℝ)^1545 := by
    have hnat : (5251974467 : ℕ)^2057*100000000000000^1545 ≤ 42426760358043^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251974467 10000000000 42426760358043 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108968777/5000000000 : ℝ), (1351891607/2500000000 : ℝ), (5251974467/10000000000 : ℝ)] ![(673243896557/5000000000000 : ℝ), (44108361691751/100000000000000 : ℝ), (42426760358043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108968777/5000000000 : ℝ)|^2057 ≤ (673243896557/5000000000000 : ℝ)^1545
        have hw : |(-1108968777/5000000000 : ℝ)|=(1108968777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351891607/2500000000 : ℝ)|^2057 ≤ (44108361691751/100000000000000 : ℝ)^1545
        have hw : |(1351891607/2500000000 : ℝ)|=(1351891607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5251974467/10000000000 : ℝ)|^2057 ≤ (42426760358043/100000000000000 : ℝ)^1545
        have hw : |(5251974467/10000000000 : ℝ)|=(5251974467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_1 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674094371/5000000000 : ℝ)*x 0 + (-229710653/1000000000 : ℝ)*x 1 + (328248407/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674094371/5000000000 : ℝ)^2057 ≤ (43464703485009/100000000000000 : ℝ)^1545 := by
    have hnat : (2674094371 : ℕ)^2057*100000000000000^1545 ≤ 43464703485009^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674094371 5000000000 43464703485009 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229710653/1000000000 : ℝ)^2057 ≤ (14108535658569/100000000000000 : ℝ)^1545 := by
    have hnat : (229710653 : ℕ)^2057*100000000000000^1545 ≤ 14108535658569^1545*1000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229710653 1000000000 14108535658569 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328248407/625000000 : ℝ)^2057 ≤ (2651672552627/6250000000000 : ℝ)^1545 := by
    have hnat : (328248407 : ℕ)^2057*6250000000000^1545 ≤ 2651672552627^1545*625000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328248407 625000000 2651672552627 6250000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674094371/5000000000 : ℝ), (-229710653/1000000000 : ℝ), (328248407/625000000 : ℝ)] ![(43464703485009/100000000000000 : ℝ), (14108535658569/100000000000000 : ℝ), (2651672552627/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674094371/5000000000 : ℝ)|^2057 ≤ (43464703485009/100000000000000 : ℝ)^1545
        have hw : |(2674094371/5000000000 : ℝ)|=(2674094371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-229710653/1000000000 : ℝ)|^2057 ≤ (14108535658569/100000000000000 : ℝ)^1545
        have hw : |(-229710653/1000000000 : ℝ)|=(229710653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328248407/625000000 : ℝ)|^2057 ≤ (2651672552627/6250000000000 : ℝ)^1545
        have hw : |(328248407/625000000 : ℝ)|=(328248407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_2 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213927553/400000000 : ℝ)*x 0 + (1050394881/2000000000 : ℝ)*x 1 + (-3589229/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213927553/400000000 : ℝ)^2057 ≤ (43464704383087/100000000000000 : ℝ)^1545 := by
    have hnat : (213927553 : ℕ)^2057*100000000000000^1545 ≤ 43464704383087^1545*400000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213927553 400000000 43464704383087 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050394881/2000000000 : ℝ)^2057 ≤ (42426759691213/100000000000000 : ℝ)^1545 := by
    have hnat : (1050394881 : ℕ)^2057*100000000000000^1545 ≤ 42426759691213^1545*2000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050394881 2000000000 42426759691213 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3589229/15625000 : ℝ)^2057 ≤ (14108535903887/100000000000000 : ℝ)^1545 := by
    have hnat : (3589229 : ℕ)^2057*100000000000000^1545 ≤ 14108535903887^1545*15625000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3589229 15625000 14108535903887 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213927553/400000000 : ℝ), (1050394881/2000000000 : ℝ), (-3589229/15625000 : ℝ)] ![(43464704383087/100000000000000 : ℝ), (42426759691213/100000000000000 : ℝ), (14108535903887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213927553/400000000 : ℝ)|^2057 ≤ (43464704383087/100000000000000 : ℝ)^1545
        have hw : |(213927553/400000000 : ℝ)|=(213927553/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050394881/2000000000 : ℝ)|^2057 ≤ (42426759691213/100000000000000 : ℝ)^1545
        have hw : |(1050394881/2000000000 : ℝ)|=(1050394881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3589229/15625000 : ℝ)|^2057 ≤ (14108535903887/100000000000000 : ℝ)^1545
        have hw : |(-3589229/15625000 : ℝ)|=(3589229/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_3 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2189641449/5000000000 : ℝ)*x 0 + (4230425737/10000000000 : ℝ)*x 1 + (2266744441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189641449/5000000000 : ℝ)^2057 ≤ (33309412518443/100000000000000 : ℝ)^1545 := by
    have hnat : (2189641449 : ℕ)^2057*100000000000000^1545 ≤ 33309412518443^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189641449 5000000000 33309412518443 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230425737/10000000000 : ℝ)^2057 ≤ (1988158111161/6250000000000 : ℝ)^1545 := by
    have hnat : (4230425737 : ℕ)^2057*6250000000000^1545 ≤ 1988158111161^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230425737 10000000000 1988158111161 6250000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266744441/5000000000 : ℝ)^2057 ≤ (2180003605711/6250000000000 : ℝ)^1545 := by
    have hnat : (2266744441 : ℕ)^2057*6250000000000^1545 ≤ 2180003605711^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266744441 5000000000 2180003605711 6250000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189641449/5000000000 : ℝ), (4230425737/10000000000 : ℝ), (2266744441/5000000000 : ℝ)] ![(33309412518443/100000000000000 : ℝ), (1988158111161/6250000000000 : ℝ), (2180003605711/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189641449/5000000000 : ℝ)|^2057 ≤ (33309412518443/100000000000000 : ℝ)^1545
        have hw : |(2189641449/5000000000 : ℝ)|=(2189641449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230425737/10000000000 : ℝ)|^2057 ≤ (1988158111161/6250000000000 : ℝ)^1545
        have hw : |(4230425737/10000000000 : ℝ)|=(4230425737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266744441/5000000000 : ℝ)|^2057 ≤ (2180003605711/6250000000000 : ℝ)^1545
        have hw : |(2266744441/5000000000 : ℝ)|=(2266744441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_4 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108973169/5000000000 : ℝ)*x 0 + (1050487207/2000000000 : ℝ)*x 1 + (5407102753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108973169/5000000000 : ℝ)^2057 ≤ (538597957201/4000000000000 : ℝ)^1545 := by
    have hnat : (1108973169 : ℕ)^2057*4000000000000^1545 ≤ 538597957201^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108973169 5000000000 538597957201 4000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050487207/2000000000 : ℝ)^2057 ≤ (21215862369431/50000000000000 : ℝ)^1545 := by
    have hnat : (1050487207 : ℕ)^2057*50000000000000^1545 ≤ 21215862369431^1545*2000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050487207 2000000000 21215862369431 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407102753/10000000000 : ℝ)^2057 ≤ (22051663155113/50000000000000 : ℝ)^1545 := by
    have hnat : (5407102753 : ℕ)^2057*50000000000000^1545 ≤ 22051663155113^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407102753 10000000000 22051663155113 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108973169/5000000000 : ℝ), (1050487207/2000000000 : ℝ), (5407102753/10000000000 : ℝ)] ![(538597957201/4000000000000 : ℝ), (21215862369431/50000000000000 : ℝ), (22051663155113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108973169/5000000000 : ℝ)|^2057 ≤ (538597957201/4000000000000 : ℝ)^1545
        have hw : |(-1108973169/5000000000 : ℝ)|=(1108973169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050487207/2000000000 : ℝ)|^2057 ≤ (21215862369431/50000000000000 : ℝ)^1545
        have hw : |(1050487207/2000000000 : ℝ)|=(1050487207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407102753/10000000000 : ℝ)|^2057 ≤ (22051663155113/50000000000000 : ℝ)^1545
        have hw : |(5407102753/10000000000 : ℝ)|=(5407102753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_5 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2654548901/5000000000 : ℝ)*x 0 + (-2141978433/10000000000 : ℝ)*x 1 + (2703551317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654548901/5000000000 : ℝ)^2057 ≤ (1076056107347/2500000000000 : ℝ)^1545 := by
    have hnat : (2654548901 : ℕ)^2057*2500000000000^1545 ≤ 1076056107347^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654548901 5000000000 1076056107347 2500000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141978433/10000000000 : ℝ)^2057 ≤ (6427215338109/50000000000000 : ℝ)^1545 := by
    have hnat : (2141978433 : ℕ)^2057*50000000000000^1545 ≤ 6427215338109^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141978433 10000000000 6427215338109 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703551317/5000000000 : ℝ)^2057 ≤ (44103325017937/100000000000000 : ℝ)^1545 := by
    have hnat : (2703551317 : ℕ)^2057*100000000000000^1545 ≤ 44103325017937^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703551317 5000000000 44103325017937 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654548901/5000000000 : ℝ), (-2141978433/10000000000 : ℝ), (2703551317/5000000000 : ℝ)] ![(1076056107347/2500000000000 : ℝ), (6427215338109/50000000000000 : ℝ), (44103325017937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654548901/5000000000 : ℝ)|^2057 ≤ (1076056107347/2500000000000 : ℝ)^1545
        have hw : |(2654548901/5000000000 : ℝ)|=(2654548901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141978433/10000000000 : ℝ)|^2057 ≤ (6427215338109/50000000000000 : ℝ)^1545
        have hw : |(-2141978433/10000000000 : ℝ)|=(2141978433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703551317/5000000000 : ℝ)|^2057 ≤ (44103325017937/100000000000000 : ℝ)^1545
        have hw : |(2703551317/5000000000 : ℝ)|=(2703551317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_6 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327274449/2500000000 : ℝ)*x 0 + (2703551341/5000000000 : ℝ)*x 1 + (-17135827/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327274449/2500000000 : ℝ)^2057 ≤ (10760561057279/25000000000000 : ℝ)^1545 := by
    have hnat : (1327274449 : ℕ)^2057*25000000000000^1545 ≤ 10760561057279^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327274449 2500000000 10760561057279 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703551341/5000000000 : ℝ)^2057 ≤ (11025831384799/25000000000000 : ℝ)^1545 := by
    have hnat : (2703551341 : ℕ)^2057*25000000000000^1545 ≤ 11025831384799^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703551341 5000000000 11025831384799 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17135827/80000000 : ℝ)^2057 ≤ (6427215106401/50000000000000 : ℝ)^1545 := by
    have hnat : (17135827 : ℕ)^2057*50000000000000^1545 ≤ 6427215106401^1545*80000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17135827 80000000 6427215106401 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327274449/2500000000 : ℝ), (2703551341/5000000000 : ℝ), (-17135827/80000000 : ℝ)] ![(10760561057279/25000000000000 : ℝ), (11025831384799/25000000000000 : ℝ), (6427215106401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327274449/2500000000 : ℝ)|^2057 ≤ (10760561057279/25000000000000 : ℝ)^1545
        have hw : |(1327274449/2500000000 : ℝ)|=(1327274449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703551341/5000000000 : ℝ)|^2057 ≤ (11025831384799/25000000000000 : ℝ)^1545
        have hw : |(2703551341/5000000000 : ℝ)|=(2703551341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17135827/80000000 : ℝ)|^2057 ≤ (6427215106401/50000000000000 : ℝ)^1545
        have hw : |(-17135827/80000000 : ℝ)|=(17135827/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s4_7 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4379299661/10000000000 : ℝ)*x 0 + (906517823/2000000000 : ℝ)*x 1 + (2115664677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379299661/10000000000 : ℝ)^2057 ≤ (1665479113657/5000000000000 : ℝ)^1545 := by
    have hnat : (4379299661 : ℕ)^2057*5000000000000^1545 ≤ 1665479113657^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379299661 10000000000 1665479113657 5000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906517823/2000000000 : ℝ)^2057 ≤ (1394833647487/4000000000000 : ℝ)^1545 := by
    have hnat : (906517823 : ℕ)^2057*4000000000000^1545 ≤ 1394833647487^1545*2000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906517823 2000000000 1394833647487 4000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115664677/5000000000 : ℝ)^2057 ≤ (7954894131143/25000000000000 : ℝ)^1545 := by
    have hnat : (2115664677 : ℕ)^2057*25000000000000^1545 ≤ 7954894131143^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115664677 5000000000 7954894131143 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379299661/10000000000 : ℝ), (906517823/2000000000 : ℝ), (2115664677/5000000000 : ℝ)] ![(1665479113657/5000000000000 : ℝ), (1394833647487/4000000000000 : ℝ), (7954894131143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379299661/10000000000 : ℝ)|^2057 ≤ (1665479113657/5000000000000 : ℝ)^1545
        have hw : |(4379299661/10000000000 : ℝ)|=(4379299661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906517823/2000000000 : ℝ)|^2057 ≤ (1394833647487/4000000000000 : ℝ)^1545
        have hw : |(906517823/2000000000 : ℝ)|=(906517823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115664677/5000000000 : ℝ)|^2057 ≤ (7954894131143/25000000000000 : ℝ)^1545
        have hw : |(2115664677/5000000000 : ℝ)|=(2115664677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1035_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2573/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5477/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14951/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2573/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14951/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2573/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14951/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2573/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14951/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2573/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14951/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2573/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14951/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2573/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2573/25000 : ℝ) ^ (8227/2048 : ℝ) ≤ (5396260292154489/50000000000000000000 : ℝ) := by
    have hpowers : (2573/25000 : ℝ)^8227 ≤ (5396260292154489/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2573 : ℕ)^8227*50000000000000000000^2048 ≤ 5396260292154489^2048*25000^8227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2573 25000 5396260292154489 50000000000000000000 8227 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2573/25000 : ℝ)) (X := (5396260292154489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14951/100000 : ℝ) ^ (8227/2048 : ℝ) ≤ (48370013581699997/100000000000000000000 : ℝ) := by
    have hpowers : (14951/100000 : ℝ)^8227 ≤ (48370013581699997/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14951 : ℕ)^8227*100000000000000000000^2048 ≤ 48370013581699997^2048*100000^8227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14951 100000 48370013581699997 100000000000000000000 8227 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14951/100000 : ℝ)) (X := (48370013581699997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005396260292154489/25000000000000000000 : ℝ) ≤ (10000537286756667/10000000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (25005396260292154489/25000000000000000000 : ℝ)^2048 ≤ (10000537286756667/10000000000000000 : ℝ)^8227 := by
      have hnat : (25005396260292154489 : ℕ)^2048*10000000000000000^8227 ≤ 10000537286756667^8227*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005396260292154489 25000000000000000000 10000537286756667 10000000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537286756667/10000000000000000 : ℝ)) (X := (25005396260292154489/25000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002366501366640359/4000000000000000000 : ℝ) ≤ (500073622194947/500000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (4002366501366640359/4000000000000000000 : ℝ)^2048 ≤ (500073622194947/500000000000000 : ℝ)^8227 := by
      have hnat : (4002366501366640359 : ℕ)^2048*500000000000000^8227 ≤ 500073622194947^8227*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002366501366640359 4000000000000000000 500073622194947 500000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500073622194947/500000000000000 : ℝ)) (X := (4002366501366640359/4000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048370013581699997/50000000000000000000 : ℝ) ≤ (10002407601041213/10000000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (50048370013581699997/50000000000000000000 : ℝ)^2048 ≤ (10002407601041213/10000000000000000 : ℝ)^8227 := by
      have hnat : (50048370013581699997 : ℕ)^2048*10000000000000000^8227 ≤ 10002407601041213^8227*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048370013581699997 50000000000000000000 10002407601041213 10000000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002407601041213/10000000000000000 : ℝ)) (X := (50048370013581699997/50000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5396260292154489/50000000000000000000 : ℝ) ≤ ((46573253944382764121/46590000000000000000 : ℝ)+2*(935157142273/465900000000000 : ℝ)*(2573/25000 : ℝ))^(8227/2048 : ℝ) := by
    rw [show (46573253944382764121/46590000000000000000 : ℝ)+2*(935157142273/465900000000000 : ℝ)*(2573/25000 : ℝ)=(10000537286756667/10000000000000000 : ℝ) by norm_num, show 1+2*(5396260292154489/50000000000000000000 : ℝ)=(25005396260292154489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48370013581699997/100000000000000000000 : ℝ)+(5396260292154489/50000000000000000000 : ℝ) ≤ ((46573253944382764121/46590000000000000000 : ℝ)+(935157142273/465900000000000 : ℝ)*((14951/100000 : ℝ)+(2573/25000 : ℝ)))^(8227/2048 : ℝ) := by
    rw [show (46573253944382764121/46590000000000000000 : ℝ)+(935157142273/465900000000000 : ℝ)*((14951/100000 : ℝ)+(2573/25000 : ℝ))=(500073622194947/500000000000000 : ℝ) by norm_num, show 1+(48370013581699997/100000000000000000000 : ℝ)+(5396260292154489/50000000000000000000 : ℝ)=(4002366501366640359/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48370013581699997/100000000000000000000 : ℝ) ≤ ((46573253944382764121/46590000000000000000 : ℝ)+2*(935157142273/465900000000000 : ℝ)*(14951/100000 : ℝ))^(8227/2048 : ℝ) := by
    rw [show (46573253944382764121/46590000000000000000 : ℝ)+2*(935157142273/465900000000000 : ℝ)*(14951/100000 : ℝ)=(10002407601041213/10000000000000000 : ℝ) by norm_num, show 1+2*(48370013581699997/100000000000000000000 : ℝ)=(50048370013581699997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46573253944382764121/46590000000000000000 : ℝ)*(X 1 0+X 2 0)+(935157142273/465900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (2573/25000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (46573253944382764121/46590000000000000000 : ℝ)) (alpha := (935157142273/465900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46573253944382764121/46590000000000000000 : ℝ)*(X 0 1+X 2 1)+(935157142273/465900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (2573/25000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (46573253944382764121/46590000000000000000 : ℝ)) (alpha := (935157142273/465900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46573253944382764121/46590000000000000000 : ℝ)*(X 0 2+X 1 2)+(935157142273/465900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (2573/25000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (46573253944382764121/46590000000000000000 : ℝ)) (alpha := (935157142273/465900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1108968777/5000000000 : ℝ)*X 0 0+(1351891607/2500000000 : ℝ)*X 0 1+(5251974467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674094371/5000000000 : ℝ)*X 1 0+(-229710653/1000000000 : ℝ)*X 1 1+(328248407/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213927553/400000000 : ℝ)*X 2 0+(1050394881/2000000000 : ℝ)*X 2 1+(-3589229/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189641449/5000000000 : ℝ)*X 0 0+(4230425737/10000000000 : ℝ)*X 0 1+(2266744441/5000000000 : ℝ)*X 0 2+(2189641449/5000000000 : ℝ)*X 1 0+(4230425737/10000000000 : ℝ)*X 1 1+(2266744441/5000000000 : ℝ)*X 1 2+(2189641449/5000000000 : ℝ)*X 2 0+(4230425737/10000000000 : ℝ)*X 2 1+(2266744441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1108973169/5000000000 : ℝ)*X 0 0+(1050487207/2000000000 : ℝ)*X 0 1+(5407102753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654548901/5000000000 : ℝ)*X 1 0+(-2141978433/10000000000 : ℝ)*X 1 1+(2703551317/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327274449/2500000000 : ℝ)*X 2 0+(2703551341/5000000000 : ℝ)*X 2 1+(-17135827/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379299661/10000000000 : ℝ)*X 0 0+(906517823/2000000000 : ℝ)*X 0 1+(2115664677/5000000000 : ℝ)*X 0 2+(4379299661/10000000000 : ℝ)*X 1 0+(906517823/2000000000 : ℝ)*X 1 1+(2115664677/5000000000 : ℝ)*X 1 2+(4379299661/10000000000 : ℝ)*X 2 0+(906517823/2000000000 : ℝ)*X 2 1+(2115664677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59772351094427179667564789/6212000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1009016931/50000000000000 : ℝ)*(base19) + (63567703/3125000000000 : ℝ)*(base23) + (11179349/25000000000000 : ℝ)*(lower2) + (32123179/12500000000000 : ℝ)*(upper3) + (17222943/10000000000000 : ℝ)*(upper5) + (38907418988291/800000000000 : ℝ)*(major0) + (38907418988291/800000000000 : ℝ)*(major1) + (38907418988291/800000000000 : ℝ)*(major2) + (3213557787129839/50000000000000 : ℝ)*(sp0) + (6427160620783857/100000000000000 : ℝ)*(sp1) + (6427160604651223/100000000000000 : ℝ)*(sp2) + (329966587015001/10000000000000 : ℝ)*(sp3) + (47064558041/100000000000000 : ℝ)*(sp4) + (12958684533/50000000000000 : ℝ)*(sp7) + (824922946879769/25000000000000 : ℝ)*(f.failure) + (160679065970443/2500000000000 : ℝ)*(f.sum) + (4855292926451/4659000000000000000000000000 : ℝ)*base65 + (27944206455239737/12424000000000000000000000000000 : ℝ)*base67 + (91402714252856263/12424000000000000000000000000000 : ℝ)*base70 + (16420549868735737/12424000000000000000000000000000 : ℝ)*base71 + (1424543597647/186360000000000000000000000 : ℝ)*base74 + (21382056030303737/12424000000000000000000000000000 : ℝ)*base75 + (33212268182391737/12424000000000000000000000000000 : ℝ)*base77 + (40930097367864263/12424000000000000000000000000000 : ℝ)*base80 + (6953246191261/4659000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (26468457/2500000000000000000000 : ℝ)*base89 + (26468457/2500000000000000000000 : ℝ)*base91 + (26468457/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56818763764425602495393/7765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1667169747/100000000000000 : ℝ)*(base19) + (446903089/25000000000000 : ℝ)*(base23) + (8751093/10000000000000 : ℝ)*(upper2) + (10876037/20000000000000 : ℝ)*(upper3) + (199340311/50000000000000 : ℝ)*(upper5) + (2446228688075353/50000000000000 : ℝ)*(major0) + (2446228688075353/50000000000000 : ℝ)*(major1) + (2446228688075353/50000000000000 : ℝ)*(major2) + (20447420927/50000000000000 : ℝ)*(sp1) + (17929219317/50000000000000 : ℝ)*(sp2) + (1293105344352631/20000000000000 : ℝ)*(sp4) + (3232742079875777/50000000000000 : ℝ)*(sp5) + (6465489075712163/100000000000000 : ℝ)*(sp6) + (66387755732571/2000000000000 : ℝ)*(sp7) + (66387755732571/2000000000000 : ℝ)*(f.failure) + (1293105344352631/20000000000000 : ℝ)*(f.sum) + (61752824553731/11647500000000000000000000000 : ℝ)*base66 + (3114606432165736571/776500000000000000000000000000000 : ℝ)*base67 + (3464444139444263429/776500000000000000000000000000000 : ℝ)*base70 + (8291860087135763429/776500000000000000000000000000000 : ℝ)*base72 + (31206495062539/11647500000000000000000000000 : ℝ)*base73 + (1595732435427236571/776500000000000000000000000000000 : ℝ)*base75 + (11692981197918763429/776500000000000000000000000000000 : ℝ)*base78 + (24397544670874236571/776500000000000000000000000000000 : ℝ)*base79 + (102721788958087/23295000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (1287563/200000000000000000000 : ℝ)*base89 + (1287563/200000000000000000000 : ℝ)*base91 + (1287563/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1035_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2573/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1035_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1035_s5_0 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-277357451/1250000000 : ℝ)*x 0 + (5397907021/10000000000 : ℝ)*x 1 + (5261029327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277357451/1250000000 : ℝ)^2057 ≤ (13472331172451/100000000000000 : ℝ)^1545 := by
    have hnat : (277357451 : ℕ)^2057*100000000000000^1545 ≤ 13472331172451^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277357451 1250000000 13472331172451 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397907021/10000000000 : ℝ)^2057 ≤ (22001746394329/50000000000000 : ℝ)^1545 := by
    have hnat : (5397907021 : ℕ)^2057*50000000000000^1545 ≤ 22001746394329^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397907021 10000000000 22001746394329 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261029327/10000000000 : ℝ)^2057 ≤ (42524176026299/100000000000000 : ℝ)^1545 := by
    have hnat : (5261029327 : ℕ)^2057*100000000000000^1545 ≤ 42524176026299^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261029327 10000000000 42524176026299 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277357451/1250000000 : ℝ), (5397907021/10000000000 : ℝ), (5261029327/10000000000 : ℝ)] ![(13472331172451/100000000000000 : ℝ), (22001746394329/50000000000000 : ℝ), (42524176026299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277357451/1250000000 : ℝ)|^2057 ≤ (13472331172451/100000000000000 : ℝ)^1545
        have hw : |(-277357451/1250000000 : ℝ)|=(277357451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397907021/10000000000 : ℝ)|^2057 ≤ (22001746394329/50000000000000 : ℝ)^1545
        have hw : |(5397907021/10000000000 : ℝ)|=(5397907021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261029327/10000000000 : ℝ)|^2057 ≤ (42524176026299/100000000000000 : ℝ)^1545
        have hw : |(5261029327/10000000000 : ℝ)|=(5261029327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_1 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345790319/10000000000 : ℝ)*x 0 + (-2288361389/10000000000 : ℝ)*x 1 + (5261029353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345790319/10000000000 : ℝ)^2057 ≤ (43438753966239/100000000000000 : ℝ)^1545 := by
    have hnat : (5345790319 : ℕ)^2057*100000000000000^1545 ≤ 43438753966239^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345790319 10000000000 43438753966239 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288361389/10000000000 : ℝ)^2057 ≤ (14037069711727/100000000000000 : ℝ)^1545 := by
    have hnat : (2288361389 : ℕ)^2057*100000000000000^1545 ≤ 14037069711727^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288361389 10000000000 14037069711727 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261029353/10000000000 : ℝ)^2057 ≤ (42524176306097/100000000000000 : ℝ)^1545 := by
    have hnat : (5261029353 : ℕ)^2057*100000000000000^1545 ≤ 42524176306097^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261029353 10000000000 42524176306097 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345790319/10000000000 : ℝ), (-2288361389/10000000000 : ℝ), (5261029353/10000000000 : ℝ)] ![(43438753966239/100000000000000 : ℝ), (14037069711727/100000000000000 : ℝ), (42524176306097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345790319/10000000000 : ℝ)|^2057 ≤ (43438753966239/100000000000000 : ℝ)^1545
        have hw : |(5345790319/10000000000 : ℝ)|=(5345790319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2288361389/10000000000 : ℝ)|^2057 ≤ (14037069711727/100000000000000 : ℝ)^1545
        have hw : |(-2288361389/10000000000 : ℝ)|=(2288361389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261029353/10000000000 : ℝ)|^2057 ≤ (42524176306097/100000000000000 : ℝ)^1545
        have hw : |(5261029353/10000000000 : ℝ)|=(5261029353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_2 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534579031/1000000000 : ℝ)*x 0 + (657628659/1250000000 : ℝ)*x 1 + (-572090377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534579031/1000000000 : ℝ)^2057 ≤ (5429844233609/12500000000000 : ℝ)^1545 := by
    have hnat : (534579031 : ℕ)^2057*12500000000000^1545 ≤ 5429844233609^1545*1000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534579031 1000000000 5429844233609 12500000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657628659/1250000000 : ℝ)^2057 ≤ (42524175434419/100000000000000 : ℝ)^1545 := by
    have hnat : (657628659 : ℕ)^2057*100000000000000^1545 ≤ 42524175434419^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657628659 1250000000 42524175434419 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572090377/2500000000 : ℝ)^2057 ≤ (14037070683589/100000000000000 : ℝ)^1545 := by
    have hnat : (572090377 : ℕ)^2057*100000000000000^1545 ≤ 14037070683589^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572090377 2500000000 14037070683589 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534579031/1000000000 : ℝ), (657628659/1250000000 : ℝ), (-572090377/2500000000 : ℝ)] ![(5429844233609/12500000000000 : ℝ), (42524175434419/100000000000000 : ℝ), (14037070683589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534579031/1000000000 : ℝ)|^2057 ≤ (5429844233609/12500000000000 : ℝ)^1545
        have hw : |(534579031/1000000000 : ℝ)|=(534579031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657628659/1250000000 : ℝ)|^2057 ≤ (42524175434419/100000000000000 : ℝ)^1545
        have hw : |(657628659/1250000000 : ℝ)|=(657628659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-572090377/2500000000 : ℝ)|^2057 ≤ (14037070683589/100000000000000 : ℝ)^1545
        have hw : |(-572090377/2500000000 : ℝ)|=(572090377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_3 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (547477083/1250000000 : ℝ)*x 0 + (531072623/1250000000 : ℝ)*x 1 + (2257596317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547477083/1250000000 : ℝ)^2057 ≤ (33314817938601/100000000000000 : ℝ)^1545 := by
    have hnat : (547477083 : ℕ)^2057*100000000000000^1545 ≤ 33314817938601^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547477083 1250000000 33314817938601 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531072623/1250000000 : ℝ)^2057 ≤ (15996208715513/50000000000000 : ℝ)^1545 := by
    have hnat : (531072623 : ℕ)^2057*50000000000000^1545 ≤ 15996208715513^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531072623 1250000000 15996208715513 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257596317/5000000000 : ℝ)^2057 ≤ (34692764621669/100000000000000 : ℝ)^1545 := by
    have hnat : (2257596317 : ℕ)^2057*100000000000000^1545 ≤ 34692764621669^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257596317 5000000000 34692764621669 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547477083/1250000000 : ℝ), (531072623/1250000000 : ℝ), (2257596317/5000000000 : ℝ)] ![(33314817938601/100000000000000 : ℝ), (15996208715513/50000000000000 : ℝ), (34692764621669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547477083/1250000000 : ℝ)|^2057 ≤ (33314817938601/100000000000000 : ℝ)^1545
        have hw : |(547477083/1250000000 : ℝ)|=(547477083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531072623/1250000000 : ℝ)|^2057 ≤ (15996208715513/50000000000000 : ℝ)^1545
        have hw : |(531072623/1250000000 : ℝ)|=(531072623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257596317/5000000000 : ℝ)|^2057 ≤ (34692764621669/100000000000000 : ℝ)^1545
        have hw : |(2257596317/5000000000 : ℝ)|=(2257596317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_4 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-5547163/25000000 : ℝ)*x 0 + (1315346709/2500000000 : ℝ)*x 1 + (5397548369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5547163/25000000 : ℝ)^2057 ≤ (1347237637741/10000000000000 : ℝ)^1545 := by
    have hnat : (5547163 : ℕ)^2057*10000000000000^1545 ≤ 1347237637741^1545*25000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547163 25000000 1347237637741 10000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315346709/2500000000 : ℝ)^2057 ≤ (2126401169331/5000000000000 : ℝ)^1545 := by
    have hnat : (1315346709 : ℕ)^2057*5000000000000^1545 ≤ 2126401169331^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315346709 2500000000 2126401169331 5000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397548369/10000000000 : ℝ)^2057 ≤ (21999800111109/50000000000000 : ℝ)^1545 := by
    have hnat : (5397548369 : ℕ)^2057*50000000000000^1545 ≤ 21999800111109^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397548369 10000000000 21999800111109 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5547163/25000000 : ℝ), (1315346709/2500000000 : ℝ), (5397548369/10000000000 : ℝ)] ![(1347237637741/10000000000000 : ℝ), (2126401169331/5000000000000 : ℝ), (21999800111109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5547163/25000000 : ℝ)|^2057 ≤ (1347237637741/10000000000000 : ℝ)^1545
        have hw : |(-5547163/25000000 : ℝ)|=(5547163/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315346709/2500000000 : ℝ)|^2057 ≤ (2126401169331/5000000000000 : ℝ)^1545
        have hw : |(1315346709/2500000000 : ℝ)|=(1315346709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397548369/10000000000 : ℝ)|^2057 ≤ (21999800111109/50000000000000 : ℝ)^1545
        have hw : |(5397548369/10000000000 : ℝ)|=(5397548369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_5 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531139947/1000000000 : ℝ)*x 0 + (-537960839/2500000000 : ℝ)*x 1 + (21590193/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531139947/1000000000 : ℝ)^2057 ≤ (43067090144123/100000000000000 : ℝ)^1545 := by
    have hnat : (531139947 : ℕ)^2057*100000000000000^1545 ≤ 43067090144123^1545*1000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531139947 1000000000 43067090144123 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537960839/2500000000 : ℝ)^2057 ≤ (3233327728517/25000000000000 : ℝ)^1545 := by
    have hnat : (537960839 : ℕ)^2057*25000000000000^1545 ≤ 3233327728517^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537960839 2500000000 3233327728517 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21590193/40000000 : ℝ)^2057 ≤ (21999799465343/50000000000000 : ℝ)^1545 := by
    have hnat : (21590193 : ℕ)^2057*50000000000000^1545 ≤ 21999799465343^1545*40000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21590193 40000000 21999799465343 50000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531139947/1000000000 : ℝ), (-537960839/2500000000 : ℝ), (21590193/40000000 : ℝ)] ![(43067090144123/100000000000000 : ℝ), (3233327728517/25000000000000 : ℝ), (21999799465343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531139947/1000000000 : ℝ)|^2057 ≤ (43067090144123/100000000000000 : ℝ)^1545
        have hw : |(531139947/1000000000 : ℝ)|=(531139947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537960839/2500000000 : ℝ)|^2057 ≤ (3233327728517/25000000000000 : ℝ)^1545
        have hw : |(-537960839/2500000000 : ℝ)|=(537960839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21590193/40000000 : ℝ)|^2057 ≤ (21999799465343/50000000000000 : ℝ)^1545
        have hw : |(21590193/40000000 : ℝ)|=(21590193/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_6 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311400007/10000000000 : ℝ)*x 0 + (2698774061/5000000000 : ℝ)*x 1 + (-537960701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311400007/10000000000 : ℝ)^2057 ≤ (43067095941301/100000000000000 : ℝ)^1545 := by
    have hnat : (5311400007 : ℕ)^2057*100000000000000^1545 ≤ 43067095941301^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311400007 10000000000 43067095941301 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698774061/5000000000 : ℝ)^2057 ≤ (10999899385369/25000000000000 : ℝ)^1545 := by
    have hnat : (2698774061 : ℕ)^2057*25000000000000^1545 ≤ 10999899385369^1545*5000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698774061 5000000000 10999899385369 25000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537960701/2500000000 : ℝ)^2057 ≤ (129333064969/1000000000000 : ℝ)^1545 := by
    have hnat : (537960701 : ℕ)^2057*1000000000000^1545 ≤ 129333064969^1545*2500000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537960701 2500000000 129333064969 1000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311400007/10000000000 : ℝ), (2698774061/5000000000 : ℝ), (-537960701/2500000000 : ℝ)] ![(43067095941301/100000000000000 : ℝ), (10999899385369/25000000000000 : ℝ), (129333064969/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311400007/10000000000 : ℝ)|^2057 ≤ (43067095941301/100000000000000 : ℝ)^1545
        have hw : |(5311400007/10000000000 : ℝ)|=(5311400007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698774061/5000000000 : ℝ)|^2057 ≤ (10999899385369/25000000000000 : ℝ)^1545
        have hw : |(2698774061/5000000000 : ℝ)|=(2698774061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537960701/2500000000 : ℝ)|^2057 ≤ (129333064969/1000000000000 : ℝ)^1545
        have hw : |(-537960701/2500000000 : ℝ)|=(537960701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1035_s5_7 (p : ℝ) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ)) (x : Fin 3 → ℝ) :
    (136869591/312500000 : ℝ)*x 0 + (564312079/1250000000 : ℝ)*x 1 + (4249280777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136869591/312500000 : ℝ)^2057 ≤ (33314921721693/100000000000000 : ℝ)^1545 := by
    have hnat : (136869591 : ℕ)^2057*100000000000000^1545 ≤ 33314921721693^1545*312500000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136869591 312500000 33314921721693 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564312079/1250000000 : ℝ)^2057 ≤ (34685644821107/100000000000000 : ℝ)^1545 := by
    have hnat : (564312079 : ℕ)^2057*100000000000000^1545 ≤ 34685644821107^1545*1250000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564312079 1250000000 34685644821107 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249280777/10000000000 : ℝ)^2057 ≤ (31999433444443/100000000000000 : ℝ)^1545 := by
    have hnat : (4249280777 : ℕ)^2057*100000000000000^1545 ≤ 31999433444443^1545*10000000000^2057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249280777 10000000000 31999433444443 100000000000000 2057 1545 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2057/512 : ℝ)) 2057 1545 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136869591/312500000 : ℝ), (564312079/1250000000 : ℝ), (4249280777/10000000000 : ℝ)] ![(33314921721693/100000000000000 : ℝ), (34685644821107/100000000000000 : ℝ), (31999433444443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136869591/312500000 : ℝ)|^2057 ≤ (33314921721693/100000000000000 : ℝ)^1545
        have hw : |(136869591/312500000 : ℝ)|=(136869591/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564312079/1250000000 : ℝ)|^2057 ≤ (34685644821107/100000000000000 : ℝ)^1545
        have hw : |(564312079/1250000000 : ℝ)|=(564312079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249280777/10000000000 : ℝ)|^2057 ≤ (31999433444443/100000000000000 : ℝ)^1545
        have hw : |(4249280777/10000000000 : ℝ)|=(4249280777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1035_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5477/50000 : ℝ) ^ (8227/2048 : ℝ) ≤ (6931821948345667/50000000000000000000 : ℝ) := by
    have hpowers : (5477/50000 : ℝ)^8227 ≤ (6931821948345667/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5477 : ℕ)^8227*50000000000000000000^2048 ≤ 6931821948345667^2048*50000^8227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5477 50000 6931821948345667 50000000000000000000 8227 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5477/50000 : ℝ)) (X := (6931821948345667/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14249/100000 : ℝ) ^ (8227/2048 : ℝ) ≤ (39872719108965897/100000000000000000000 : ℝ) := by
    have hpowers : (14249/100000 : ℝ)^8227 ≤ (39872719108965897/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14249 : ℕ)^8227*100000000000000000000^2048 ≤ 39872719108965897^2048*100000^8227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14249 100000 39872719108965897 100000000000000000000 8227 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14249/100000 : ℝ)) (X := (39872719108965897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006931821948345667/25000000000000000000 : ℝ) ≤ (5000345080670849/5000000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (25006931821948345667/25000000000000000000 : ℝ)^2048 ≤ (5000345080670849/5000000000000000 : ℝ)^8227 := by
      have hnat : (25006931821948345667 : ℕ)^2048*5000000000000000^8227 ≤ 5000345080670849^8227*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006931821948345667 25000000000000000000 5000345080670849 5000000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000345080670849/5000000000000000 : ℝ)) (X := (25006931821948345667/25000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053736363005657231/100000000000000000000 : ℝ) ≤ (80010699391779/80000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (100053736363005657231/100000000000000000000 : ℝ)^2048 ≤ (80010699391779/80000000000000 : ℝ)^8227 := by
      have hnat : (100053736363005657231 : ℕ)^2048*80000000000000^8227 ≤ 80010699391779^8227*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053736363005657231 100000000000000000000 80010699391779 80000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80010699391779/80000000000000 : ℝ)) (X := (100053736363005657231/100000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039872719108965897/50000000000000000000 : ℝ) ≤ (2500496171650763/2500000000000000 : ℝ) ^ (8227/2048 : ℝ) := by
    have hpowers : (50039872719108965897/50000000000000000000 : ℝ)^2048 ≤ (2500496171650763/2500000000000000 : ℝ)^8227 := by
      have hnat : (50039872719108965897 : ℕ)^2048*2500000000000000^8227 ≤ 2500496171650763^8227*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039872719108965897 50000000000000000000 2500496171650763 2500000000000000 2048 8227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500496171650763/2500000000000000 : ℝ)) (X := (50039872719108965897/50000000000000000000 : ℝ)) (by norm_num) 8227 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6931821948345667/50000000000000000000 : ℝ) ≤ ((16469046925954011597/16475000000000000000 : ℝ)+2*(647262630677/329500000000000 : ℝ)*(5477/50000 : ℝ))^(8227/2048 : ℝ) := by
    rw [show (16469046925954011597/16475000000000000000 : ℝ)+2*(647262630677/329500000000000 : ℝ)*(5477/50000 : ℝ)=(5000345080670849/5000000000000000 : ℝ) by norm_num, show 1+2*(6931821948345667/50000000000000000000 : ℝ)=(25006931821948345667/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39872719108965897/100000000000000000000 : ℝ)+(6931821948345667/50000000000000000000 : ℝ) ≤ ((16469046925954011597/16475000000000000000 : ℝ)+(647262630677/329500000000000 : ℝ)*((14249/100000 : ℝ)+(5477/50000 : ℝ)))^(8227/2048 : ℝ) := by
    rw [show (16469046925954011597/16475000000000000000 : ℝ)+(647262630677/329500000000000 : ℝ)*((14249/100000 : ℝ)+(5477/50000 : ℝ))=(80010699391779/80000000000000 : ℝ) by norm_num, show 1+(39872719108965897/100000000000000000000 : ℝ)+(6931821948345667/50000000000000000000 : ℝ)=(100053736363005657231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39872719108965897/100000000000000000000 : ℝ) ≤ ((16469046925954011597/16475000000000000000 : ℝ)+2*(647262630677/329500000000000 : ℝ)*(14249/100000 : ℝ))^(8227/2048 : ℝ) := by
    rw [show (16469046925954011597/16475000000000000000 : ℝ)+2*(647262630677/329500000000000 : ℝ)*(14249/100000 : ℝ)=(2500496171650763/2500000000000000 : ℝ) by norm_num, show 1+2*(39872719108965897/100000000000000000000 : ℝ)=(50039872719108965897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16469046925954011597/16475000000000000000 : ℝ)*(X 1 0+X 2 0)+(647262630677/329500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (16469046925954011597/16475000000000000000 : ℝ)) (alpha := (647262630677/329500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16469046925954011597/16475000000000000000 : ℝ)*(X 0 1+X 2 1)+(647262630677/329500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (16469046925954011597/16475000000000000000 : ℝ)) (alpha := (647262630677/329500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16469046925954011597/16475000000000000000 : ℝ)*(X 0 2+X 1 2)+(647262630677/329500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8227/2048 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (16469046925954011597/16475000000000000000 : ℝ)) (alpha := (647262630677/329500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-277357451/1250000000 : ℝ)*X 0 0+(5397907021/10000000000 : ℝ)*X 0 1+(5261029327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345790319/10000000000 : ℝ)*X 1 0+(-2288361389/10000000000 : ℝ)*X 1 1+(5261029353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534579031/1000000000 : ℝ)*X 2 0+(657628659/1250000000 : ℝ)*X 2 1+(-572090377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547477083/1250000000 : ℝ)*X 0 0+(531072623/1250000000 : ℝ)*X 0 1+(2257596317/5000000000 : ℝ)*X 0 2+(547477083/1250000000 : ℝ)*X 1 0+(531072623/1250000000 : ℝ)*X 1 1+(2257596317/5000000000 : ℝ)*X 1 2+(547477083/1250000000 : ℝ)*X 2 0+(531072623/1250000000 : ℝ)*X 2 1+(2257596317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-5547163/25000000 : ℝ)*X 0 0+(1315346709/2500000000 : ℝ)*X 0 1+(5397548369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531139947/1000000000 : ℝ)*X 1 0+(-537960839/2500000000 : ℝ)*X 1 1+(21590193/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311400007/10000000000 : ℝ)*X 2 0+(2698774061/5000000000 : ℝ)*X 2 1+(-537960701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136869591/312500000 : ℝ)*X 0 0+(564312079/1250000000 : ℝ)*X 0 1+(4249280777/10000000000 : ℝ)*X 0 2+(136869591/312500000 : ℝ)*X 1 0+(564312079/1250000000 : ℝ)*X 1 1+(4249280777/10000000000 : ℝ)*X 1 2+(136869591/312500000 : ℝ)*X 2 0+(564312079/1250000000 : ℝ)*X 2 1+(4249280777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1035_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4674958650673823772069948249/411875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1034282379/50000000000000 : ℝ)*(base19) + (888599237/50000000000000 : ℝ)*(base23) + (37295751/25000000000000 : ℝ)*(lower2) + (418512587/100000000000000 : ℝ)*(upper3) + (28395803/100000000000000 : ℝ)*(upper5) + (5528360406499561/100000000000000 : ℝ)*(major0) + (5528360406499561/100000000000000 : ℝ)*(major1) + (5528360406499561/100000000000000 : ℝ)*(major2) + (1826462171952949/25000000000000 : ℝ)*(sp0) + (3652944580264151/50000000000000 : ℝ)*(sp1) + (3652944725947293/50000000000000 : ℝ)*(sp2) + (937699249729237/25000000000000 : ℝ)*(sp3) + (8508256253/20000000000000 : ℝ)*(sp4) + (32206641411/100000000000000 : ℝ)*(sp7) + (93770730138959/2500000000000 : ℝ)*(f.failure) + (7305891229093061/100000000000000 : ℝ)*(f.sum) + (32262013402803/16475000000000000000000000000 : ℝ)*base66 + (21979000115609258917/1647500000000000000000000000000000 : ℝ)*base67 + (8063270083249258917/1647500000000000000000000000000000 : ℝ)*base69 + (13137047519314258917/1647500000000000000000000000000000 : ℝ)*base71 + (45866509711447/16475000000000000000000000000 : ℝ)*base73 + (3902178461721758917/1647500000000000000000000000000000 : ℝ)*base75 + (11943097578680741083/1647500000000000000000000000000000 : ℝ)*base78 + (25595469976549258917/1647500000000000000000000000000000 : ℝ)*base79 + (19353998318393/4118750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3562527/250000000000000000000 : ℝ)*base89 + (3562527/250000000000000000000 : ℝ)*base91 + (3562527/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7470318903456396141934579887/411875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34358189/6250000000000 : ℝ)*(base23) + (70392787/100000000000000 : ℝ)*(lower2) + (56775073/50000000000000 : ℝ)*(upper4) + (13809061/20000000000000 : ℝ)*(upper5) + (2778692605104857/50000000000000 : ℝ)*(major0) + (2778692605104857/50000000000000 : ℝ)*(major1) + (2778692605104857/50000000000000 : ℝ)*(major2) + (1600446199/25000000000000 : ℝ)*(sp0) + (1481902833/6250000000000 : ℝ)*(sp2) + (308698203/20000000000000 : ℝ)*(sp3) + (3672120868345757/50000000000000 : ℝ)*(sp4) + (734424813847631/10000000000000 : ℝ)*(sp5) + (3672111939149979/50000000000000 : ℝ)*(sp6) + (377052013387393/10000000000000 : ℝ)*(sp7) + (1885260838682473/50000000000000 : ℝ)*(f.failure) + (734424813847631/10000000000000 : ℝ)*(f.sum) + (131574853688911/8237500000000000000000000000 : ℝ)*base66 + (9758798649436523371/823750000000000000000000000000000 : ℝ)*base68 + (686061569364023371/823750000000000000000000000000000 : ℝ)*base70 + (35878929964336523371/823750000000000000000000000000000 : ℝ)*base72 + (11700636155189/8237500000000000000000000000 : ℝ)*base73 + (169481439163476629/823750000000000000000000000000000 : ℝ)*base75 + (1408183239320976629/823750000000000000000000000000000 : ℝ)*base77 + (10094277156746523371/823750000000000000000000000000000 : ℝ)*base80 + (6843607598489/8237500000000000000000000000 : ℝ)*base81 + (50382969/5000000000000000000000 : ℝ)*base89 + (50382969/5000000000000000000000 : ℝ)*base91 + (50382969/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1035_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1035_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1035_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (107/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1035_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1035_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1035_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8227/2048 : ℝ) ≤ p) (hpb : p ≤ (2057/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147390353/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (107/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1035_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

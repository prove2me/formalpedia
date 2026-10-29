-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1621_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:14.209804+00:00
-- url     : https://prove2.me/submissions/7d73f4a0-e4a5-486b-9c4a-832411d6970d

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
theorem support_rectangle_w1621_s3_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419224309/2500000000 : ℝ)*x 0 + (5456502163/10000000000 : ℝ)*x 1 + (5181464549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419224309/2500000000 : ℝ)^4803 ≤ (10336418021273/100000000000000 : ℝ)^3779 := by
    have hnat : (419224309 : ℕ)^4803*100000000000000^3779 ≤ 10336418021273^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419224309 2500000000 10336418021273 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456502163/10000000000 : ℝ)^4803 ≤ (11576191768689/25000000000000 : ℝ)^3779 := by
    have hnat : (5456502163 : ℕ)^4803*25000000000000^3779 ≤ 11576191768689^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456502163 10000000000 11576191768689 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181464549/10000000000 : ℝ)^4803 ≤ (43358814886939/100000000000000 : ℝ)^3779 := by
    have hnat : (5181464549 : ℕ)^4803*100000000000000^3779 ≤ 43358814886939^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181464549 10000000000 43358814886939 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419224309/2500000000 : ℝ), (5456502163/10000000000 : ℝ), (5181464549/10000000000 : ℝ)] ![(10336418021273/100000000000000 : ℝ), (11576191768689/25000000000000 : ℝ), (43358814886939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419224309/2500000000 : ℝ)|^4803 ≤ (10336418021273/100000000000000 : ℝ)^3779
        have hw : |(-419224309/2500000000 : ℝ)|=(419224309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456502163/10000000000 : ℝ)|^4803 ≤ (11576191768689/25000000000000 : ℝ)^3779
        have hw : |(5456502163/10000000000 : ℝ)|=(5456502163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181464549/10000000000 : ℝ)|^4803 ≤ (43358814886939/100000000000000 : ℝ)^3779
        have hw : |(5181464549/10000000000 : ℝ)|=(5181464549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107042029/200000000 : ℝ)*x 0 + (-227332821/1250000000 : ℝ)*x 1 + (103629291/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107042029/200000000 : ℝ)^4803 ≤ (5647708534033/12500000000000 : ℝ)^3779 := by
    have hnat : (107042029 : ℕ)^4803*12500000000000^3779 ≤ 5647708534033^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107042029 200000000 5647708534033 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227332821/1250000000 : ℝ)^4803 ≤ (1145951681839/10000000000000 : ℝ)^3779 := by
    have hnat : (227332821 : ℕ)^4803*10000000000000^3779 ≤ 1145951681839^3779*1250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227332821 1250000000 1145951681839 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103629291/200000000 : ℝ)^4803 ≤ (21679407448787/50000000000000 : ℝ)^3779 := by
    have hnat : (103629291 : ℕ)^4803*50000000000000^3779 ≤ 21679407448787^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103629291 200000000 21679407448787 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107042029/200000000 : ℝ), (-227332821/1250000000 : ℝ), (103629291/200000000 : ℝ)] ![(5647708534033/12500000000000 : ℝ), (1145951681839/10000000000000 : ℝ), (21679407448787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107042029/200000000 : ℝ)|^4803 ≤ (5647708534033/12500000000000 : ℝ)^3779
        have hw : |(107042029/200000000 : ℝ)|=(107042029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227332821/1250000000 : ℝ)|^4803 ≤ (1145951681839/10000000000000 : ℝ)^3779
        have hw : |(-227332821/1250000000 : ℝ)|=(227332821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103629291/200000000 : ℝ)|^4803 ≤ (21679407448787/50000000000000 : ℝ)^3779
        have hw : |(103629291/200000000 : ℝ)|=(103629291/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352101449/10000000000 : ℝ)*x 0 + (103629291/200000000 : ℝ)*x 1 + (-1818662569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352101449/10000000000 : ℝ)^4803 ≤ (9036333652307/20000000000000 : ℝ)^3779 := by
    have hnat : (5352101449 : ℕ)^4803*20000000000000^3779 ≤ 9036333652307^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352101449 10000000000 9036333652307 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103629291/200000000 : ℝ)^4803 ≤ (21679407448787/50000000000000 : ℝ)^3779 := by
    have hnat : (103629291 : ℕ)^4803*50000000000000^3779 ≤ 21679407448787^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103629291 200000000 21679407448787 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1818662569/10000000000 : ℝ)^4803 ≤ (5729758413199/50000000000000 : ℝ)^3779 := by
    have hnat : (1818662569 : ℕ)^4803*50000000000000^3779 ≤ 5729758413199^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818662569 10000000000 5729758413199 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352101449/10000000000 : ℝ), (103629291/200000000 : ℝ), (-1818662569/10000000000 : ℝ)] ![(9036333652307/20000000000000 : ℝ), (21679407448787/50000000000000 : ℝ), (5729758413199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352101449/10000000000 : ℝ)|^4803 ≤ (9036333652307/20000000000000 : ℝ)^3779
        have hw : |(5352101449/10000000000 : ℝ)|=(5352101449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103629291/200000000 : ℝ)|^4803 ≤ (21679407448787/50000000000000 : ℝ)^3779
        have hw : |(103629291/200000000 : ℝ)|=(103629291/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1818662569/10000000000 : ℝ)|^4803 ≤ (5729758413199/50000000000000 : ℝ)^3779
        have hw : |(-1818662569/10000000000 : ℝ)|=(1818662569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210175659/500000000 : ℝ)*x 0 + (3871269223/10000000000 : ℝ)*x 1 + (4556930071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210175659/500000000 : ℝ)^4803 ≤ (33237031899013/100000000000000 : ℝ)^3779 := by
    have hnat : (210175659 : ℕ)^4803*100000000000000^3779 ≤ 33237031899013^3779*500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210175659 500000000 33237031899013 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3871269223/10000000000 : ℝ)^4803 ≤ (29934604686803/100000000000000 : ℝ)^3779 := by
    have hnat : (3871269223 : ℕ)^4803*100000000000000^3779 ≤ 29934604686803^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3871269223 10000000000 29934604686803 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556930071/10000000000 : ℝ)^4803 ≤ (3682836340391/10000000000000 : ℝ)^3779 := by
    have hnat : (4556930071 : ℕ)^4803*10000000000000^3779 ≤ 3682836340391^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556930071 10000000000 3682836340391 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210175659/500000000 : ℝ), (3871269223/10000000000 : ℝ), (4556930071/10000000000 : ℝ)] ![(33237031899013/100000000000000 : ℝ), (29934604686803/100000000000000 : ℝ), (3682836340391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210175659/500000000 : ℝ)|^4803 ≤ (33237031899013/100000000000000 : ℝ)^3779
        have hw : |(210175659/500000000 : ℝ)|=(210175659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3871269223/10000000000 : ℝ)|^4803 ≤ (29934604686803/100000000000000 : ℝ)^3779
        have hw : |(3871269223/10000000000 : ℝ)|=(3871269223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556930071/10000000000 : ℝ)|^4803 ≤ (3682836340391/10000000000000 : ℝ)^3779
        have hw : |(4556930071/10000000000 : ℝ)|=(4556930071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-83848313/500000000 : ℝ)*x 0 + (2591761883/5000000000 : ℝ)*x 1 + (4363537/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83848313/500000000 : ℝ)^4803 ≤ (10336958777907/100000000000000 : ℝ)^3779 := by
    have hnat : (83848313 : ℕ)^4803*100000000000000^3779 ≤ 10336958777907^3779*500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83848313 500000000 10336958777907 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591761883/5000000000 : ℝ)^4803 ≤ (21690358501181/50000000000000 : ℝ)^3779 := by
    have hnat : (2591761883 : ℕ)^4803*50000000000000^3779 ≤ 21690358501181^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591761883 5000000000 21690358501181 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4363537/8000000 : ℝ)^4803 ≤ (46282324196791/100000000000000 : ℝ)^3779 := by
    have hnat : (4363537 : ℕ)^4803*100000000000000^3779 ≤ 46282324196791^3779*8000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363537 8000000 46282324196791 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83848313/500000000 : ℝ), (2591761883/5000000000 : ℝ), (4363537/8000000 : ℝ)] ![(10336958777907/100000000000000 : ℝ), (21690358501181/50000000000000 : ℝ), (46282324196791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83848313/500000000 : ℝ)|^4803 ≤ (10336958777907/100000000000000 : ℝ)^3779
        have hw : |(-83848313/500000000 : ℝ)|=(83848313/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591761883/5000000000 : ℝ)|^4803 ≤ (21690358501181/50000000000000 : ℝ)^3779
        have hw : |(2591761883/5000000000 : ℝ)|=(2591761883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4363537/8000000 : ℝ)|^4803 ≤ (46282324196791/100000000000000 : ℝ)^3779
        have hw : |(4363537/8000000 : ℝ)|=(4363537/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278920571/10000000000 : ℝ)*x 0 + (-386426559/2500000000 : ℝ)*x 1 + (5454420567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278920571/10000000000 : ℝ)^4803 ≤ (22198972037179/50000000000000 : ℝ)^3779 := by
    have hnat : (5278920571 : ℕ)^4803*50000000000000^3779 ≤ 22198972037179^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278920571 10000000000 22198972037179 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386426559/2500000000 : ℝ)^4803 ≤ (4659869536271/50000000000000 : ℝ)^3779 := by
    have hnat : (386426559 : ℕ)^4803*50000000000000^3779 ≤ 4659869536271^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386426559 2500000000 4659869536271 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454420567/10000000000 : ℝ)^4803 ≤ (46282316830941/100000000000000 : ℝ)^3779 := by
    have hnat : (5454420567 : ℕ)^4803*100000000000000^3779 ≤ 46282316830941^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454420567 10000000000 46282316830941 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278920571/10000000000 : ℝ), (-386426559/2500000000 : ℝ), (5454420567/10000000000 : ℝ)] ![(22198972037179/50000000000000 : ℝ), (4659869536271/50000000000000 : ℝ), (46282316830941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278920571/10000000000 : ℝ)|^4803 ≤ (22198972037179/50000000000000 : ℝ)^3779
        have hw : |(5278920571/10000000000 : ℝ)|=(5278920571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386426559/2500000000 : ℝ)|^4803 ≤ (4659869536271/50000000000000 : ℝ)^3779
        have hw : |(-386426559/2500000000 : ℝ)|=(386426559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454420567/10000000000 : ℝ)|^4803 ≤ (46282316830941/100000000000000 : ℝ)^3779
        have hw : |(5454420567/10000000000 : ℝ)|=(5454420567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_6 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055784007/2000000000 : ℝ)*x 0 + (5454421047/10000000000 : ℝ)*x 1 + (-1545706309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055784007/2000000000 : ℝ)^4803 ≤ (22198969172419/50000000000000 : ℝ)^3779 := by
    have hnat : (1055784007 : ℕ)^4803*50000000000000^3779 ≤ 22198969172419^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055784007 2000000000 22198969172419 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454421047/10000000000 : ℝ)^4803 ≤ (46282322007527/100000000000000 : ℝ)^3779 := by
    have hnat : (5454421047 : ℕ)^4803*100000000000000^3779 ≤ 46282322007527^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454421047 10000000000 46282322007527 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1545706309/10000000000 : ℝ)^4803 ≤ (4659869815979/50000000000000 : ℝ)^3779 := by
    have hnat : (1545706309 : ℕ)^4803*50000000000000^3779 ≤ 4659869815979^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545706309 10000000000 4659869815979 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055784007/2000000000 : ℝ), (5454421047/10000000000 : ℝ), (-1545706309/10000000000 : ℝ)] ![(22198969172419/50000000000000 : ℝ), (46282322007527/100000000000000 : ℝ), (4659869815979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055784007/2000000000 : ℝ)|^4803 ≤ (22198969172419/50000000000000 : ℝ)^3779
        have hw : |(1055784007/2000000000 : ℝ)|=(1055784007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454421047/10000000000 : ℝ)|^4803 ≤ (46282322007527/100000000000000 : ℝ)^3779
        have hw : |(5454421047/10000000000 : ℝ)|=(5454421047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1545706309/10000000000 : ℝ)|^4803 ≤ (4659869815979/50000000000000 : ℝ)^3779
        have hw : |(-1545706309/10000000000 : ℝ)|=(1545706309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s3_7 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203685349/10000000000 : ℝ)*x 0 + (4551795641/10000000000 : ℝ)*x 1 + (969114449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203685349/10000000000 : ℝ)^4803 ≤ (6647752425041/20000000000000 : ℝ)^3779 := by
    have hnat : (4203685349 : ℕ)^4803*20000000000000^3779 ≤ 6647752425041^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203685349 10000000000 6647752425041 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551795641/10000000000 : ℝ)^4803 ≤ (36775631716727/100000000000000 : ℝ)^3779 := by
    have hnat : (4551795641 : ℕ)^4803*100000000000000^3779 ≤ 36775631716727^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551795641 10000000000 36775631716727 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969114449/2500000000 : ℝ)^4803 ≤ (29985606146773/100000000000000 : ℝ)^3779 := by
    have hnat : (969114449 : ℕ)^4803*100000000000000^3779 ≤ 29985606146773^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969114449 2500000000 29985606146773 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203685349/10000000000 : ℝ), (4551795641/10000000000 : ℝ), (969114449/2500000000 : ℝ)] ![(6647752425041/20000000000000 : ℝ), (36775631716727/100000000000000 : ℝ), (29985606146773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203685349/10000000000 : ℝ)|^4803 ≤ (6647752425041/20000000000000 : ℝ)^3779
        have hw : |(4203685349/10000000000 : ℝ)|=(4203685349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551795641/10000000000 : ℝ)|^4803 ≤ (36775631716727/100000000000000 : ℝ)^3779
        have hw : |(4551795641/10000000000 : ℝ)|=(4551795641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(969114449/2500000000 : ℝ)|^4803 ≤ (29985606146773/100000000000000 : ℝ)^3779
        have hw : |(969114449/2500000000 : ℝ)|=(969114449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4083/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16449/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1299/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16449/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1299/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16449/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1299/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16449/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1299/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16449/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1299/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16449/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1299/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1299/12500 : ℝ) ^ (4799/1024 : ℝ) ≤ (616137260266951/25000000000000000000 : ℝ) := by
    have hpowers : (1299/12500 : ℝ)^4799 ≤ (616137260266951/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1299 : ℕ)^4799*25000000000000000000^1024 ≤ 616137260266951^1024*12500^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1299 12500 616137260266951 25000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1299/12500 : ℝ)) (X := (616137260266951/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16449/100000 : ℝ) ^ (4799/1024 : ℝ) ≤ (21204078230461491/100000000000000000000 : ℝ) := by
    have hpowers : (16449/100000 : ℝ)^4799 ≤ (21204078230461491/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16449 : ℕ)^4799*100000000000000000000^1024 ≤ 21204078230461491^1024*100000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16449 100000 21204078230461491 100000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16449/100000 : ℝ)) (X := (21204078230461491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500616137260266951/12500000000000000000 : ℝ) ≤ (2500026293491283/2500000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (12500616137260266951/12500000000000000000 : ℝ)^1024 ≤ (2500026293491283/2500000000000000 : ℝ)^4799 := by
      have hnat : (12500616137260266951 : ℕ)^1024*2500000000000000^4799 ≤ 2500026293491283^4799*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500616137260266951 12500000000000000000 2500026293491283 2500000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500026293491283/2500000000000000 : ℝ)) (X := (12500616137260266951/12500000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004733725454305859/20000000000000000000 : ℝ) ≤ (100005049889231/100000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (20004733725454305859/20000000000000000000 : ℝ)^1024 ≤ (100005049889231/100000000000000 : ℝ)^4799 := by
      have hnat : (20004733725454305859 : ℕ)^1024*100000000000000^4799 ≤ 100005049889231^4799*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004733725454305859 20000000000000000000 100005049889231 100000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100005049889231/100000000000000 : ℝ)) (X := (20004733725454305859/20000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021204078230461491/50000000000000000000 : ℝ) ≤ (2500226200970267/2500000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50021204078230461491/50000000000000000000 : ℝ)^1024 ≤ (2500226200970267/2500000000000000 : ℝ)^4799 := by
      have hnat : (50021204078230461491 : ℕ)^1024*2500000000000000^4799 ≤ 2500226200970267^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021204078230461491 50000000000000000000 2500226200970267 2500000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500226200970267/2500000000000000 : ℝ)) (X := (50021204078230461491/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(616137260266951/25000000000000000000 : ℝ) ≤ ((1682286869017233267/1682500000000000000 : ℝ)+2*(8329478291/12618750000000 : ℝ)*(1299/12500 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (1682286869017233267/1682500000000000000 : ℝ)+2*(8329478291/12618750000000 : ℝ)*(1299/12500 : ℝ)=(2500026293491283/2500000000000000 : ℝ) by norm_num, show 1+2*(616137260266951/25000000000000000000 : ℝ)=(12500616137260266951/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21204078230461491/100000000000000000000 : ℝ)+(616137260266951/25000000000000000000 : ℝ) ≤ ((1682286869017233267/1682500000000000000 : ℝ)+(8329478291/12618750000000 : ℝ)*((16449/100000 : ℝ)+(1299/12500 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (1682286869017233267/1682500000000000000 : ℝ)+(8329478291/12618750000000 : ℝ)*((16449/100000 : ℝ)+(1299/12500 : ℝ))=(100005049889231/100000000000000 : ℝ) by norm_num, show 1+(21204078230461491/100000000000000000000 : ℝ)+(616137260266951/25000000000000000000 : ℝ)=(20004733725454305859/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21204078230461491/100000000000000000000 : ℝ) ≤ ((1682286869017233267/1682500000000000000 : ℝ)+2*(8329478291/12618750000000 : ℝ)*(16449/100000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (1682286869017233267/1682500000000000000 : ℝ)+2*(8329478291/12618750000000 : ℝ)*(16449/100000 : ℝ)=(2500226200970267/2500000000000000 : ℝ) by norm_num, show 1+2*(21204078230461491/100000000000000000000 : ℝ)=(50021204078230461491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1682286869017233267/1682500000000000000 : ℝ)*(X 1 0+X 2 0)+(8329478291/12618750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (1299/12500 : ℝ)) (hi := (16449/100000 : ℝ)) (c := (1682286869017233267/1682500000000000000 : ℝ)) (alpha := (8329478291/12618750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1682286869017233267/1682500000000000000 : ℝ)*(X 0 1+X 2 1)+(8329478291/12618750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (1299/12500 : ℝ)) (hi := (16449/100000 : ℝ)) (c := (1682286869017233267/1682500000000000000 : ℝ)) (alpha := (8329478291/12618750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1682286869017233267/1682500000000000000 : ℝ)*(X 0 2+X 1 2)+(8329478291/12618750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (1299/12500 : ℝ)) (hi := (16449/100000 : ℝ)) (c := (1682286869017233267/1682500000000000000 : ℝ)) (alpha := (8329478291/12618750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419224309/2500000000 : ℝ)*X 0 0+(5456502163/10000000000 : ℝ)*X 0 1+(5181464549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107042029/200000000 : ℝ)*X 1 0+(-227332821/1250000000 : ℝ)*X 1 1+(103629291/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352101449/10000000000 : ℝ)*X 2 0+(103629291/200000000 : ℝ)*X 2 1+(-1818662569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((210175659/500000000 : ℝ)*X 0 0+(3871269223/10000000000 : ℝ)*X 0 1+(4556930071/10000000000 : ℝ)*X 0 2+(210175659/500000000 : ℝ)*X 1 0+(3871269223/10000000000 : ℝ)*X 1 1+(4556930071/10000000000 : ℝ)*X 1 2+(210175659/500000000 : ℝ)*X 2 0+(3871269223/10000000000 : ℝ)*X 2 1+(4556930071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83848313/500000000 : ℝ)*X 0 0+(2591761883/5000000000 : ℝ)*X 0 1+(4363537/8000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278920571/10000000000 : ℝ)*X 1 0+(-386426559/2500000000 : ℝ)*X 1 1+(5454420567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055784007/2000000000 : ℝ)*X 2 0+(5454421047/10000000000 : ℝ)*X 2 1+(-1545706309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4203685349/10000000000 : ℝ)*X 0 0+(4551795641/10000000000 : ℝ)*X 0 1+(969114449/2500000000 : ℝ)*X 0 2+(4203685349/10000000000 : ℝ)*X 1 0+(4551795641/10000000000 : ℝ)*X 1 1+(969114449/2500000000 : ℝ)*X 1 2+(4203685349/10000000000 : ℝ)*X 2 0+(4551795641/10000000000 : ℝ)*X 2 1+(969114449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (141834829840627199417926377/42062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138012771/25000000000000 : ℝ)*(base19) + (128943223/25000000000000 : ℝ)*(base23) + (19052869/100000000000000 : ℝ)*(lower2) + (3362769/4000000000000 : ℝ)*(upper3) + (14296211/25000000000000 : ℝ)*(upper5) + (1273583131268223/50000000000000 : ℝ)*(major0) + (1273583131268223/50000000000000 : ℝ)*(major1) + (1273583131268223/50000000000000 : ℝ)*(major2) + (3635873249337871/100000000000000 : ℝ)*(sp0) + (72717587521599/2000000000000 : ℝ)*(sp1) + (3635879412358141/100000000000000 : ℝ)*(sp2) + (58337982804079/4000000000000 : ℝ)*(sp3) + (3339396581/50000000000000 : ℝ)*(sp4) + (22769061/781250000000 : ℝ)*(sp7) + (729226242270891/50000000000000 : ℝ)*(f.failure) + (1817939964065517/50000000000000 : ℝ)*(f.sum) + (918696731603/210312500000000000000000000 : ℝ)*base66 + (183839450048724541/84125000000000000000000000000000 : ℝ)*base67 + (875963951905974541/84125000000000000000000000000000 : ℝ)*base69 + (159578617614025459/84125000000000000000000000000000 : ℝ)*base72 + (10574384333653/3365000000000000000000000000 : ℝ)*base74 + (420541081339349541/84125000000000000000000000000000 : ℝ)*base75 + (745428137578849541/84125000000000000000000000000000 : ℝ)*base77 + (206567722501900459/84125000000000000000000000000000 : ℝ)*base80 + (1709159484167/841250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (711663/62500000000000000000 : ℝ)*base90 + (711663/62500000000000000000 : ℝ)*base92 + (711663/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1578075208770288784337/168250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1659076387/100000000000000 : ℝ)*(base19) + (54057047/4000000000000 : ℝ)*(base23) + (388421/500000000000 : ℝ)*(upper3) + (8321879/12500000000000 : ℝ)*(lower4) + (302790041/100000000000000 : ℝ)*(upper5) + (517217392038763/20000000000000 : ℝ)*(major0) + (517217392038763/20000000000000 : ℝ)*(major1) + (517217392038763/20000000000000 : ℝ)*(major2) + (15545987183/100000000000000 : ℝ)*(sp1) + (2823348729/25000000000000 : ℝ)*(sp2) + (922858992714981/25000000000000 : ℝ)*(sp4) + (1845709382898177/50000000000000 : ℝ)*(sp5) + (230713957877427/6250000000000 : ℝ)*(sp6) + (740368818441393/50000000000000 : ℝ)*(sp7) + (740368818441393/50000000000000 : ℝ)*(f.failure) + (922858992714981/25000000000000 : ℝ)*(f.sum) + (1505632666561/1009500000000000000000000000 : ℝ)*base65 + (85682084484913837/100950000000000000000000000000000 : ℝ)*base68 + (379112949378613837/100950000000000000000000000000000 : ℝ)*base70 + (348952233163513837/100950000000000000000000000000000 : ℝ)*base72 + (639219945947/1009500000000000000000000000 : ℝ)*base74 + (365787977971786163/100950000000000000000000000000000 : ℝ)*base75 + (323120481862486163/100950000000000000000000000000000 : ℝ)*base77 + (389452100951086163/100950000000000000000000000000000 : ℝ)*base79 + (185045150347/504750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (226949/62500000000000000000 : ℝ)*base90 + (226949/62500000000000000000 : ℝ)*base92 + (226949/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1621_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4083/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1621_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1621_s4_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419246779/2500000000 : ℝ)*x 0 + (5456050891/10000000000 : ℝ)*x 1 + (2590927987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419246779/2500000000 : ℝ)^4803 ≤ (10337122171831/100000000000000 : ℝ)^3779 := by
    have hnat : (419246779 : ℕ)^4803*100000000000000^3779 ≤ 10337122171831^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419246779 2500000000 10337122171831 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456050891/10000000000 : ℝ)^4803 ≤ (5787487482389/12500000000000 : ℝ)^3779 := by
    have hnat : (5456050891 : ℕ)^4803*12500000000000^3779 ≤ 5787487482389^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456050891 10000000000 5787487482389 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590927987/5000000000 : ℝ)^4803 ≤ (169386632639/390625000000 : ℝ)^3779 := by
    have hnat : (2590927987 : ℕ)^4803*390625000000^3779 ≤ 169386632639^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590927987 5000000000 169386632639 390625000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419246779/2500000000 : ℝ), (5456050891/10000000000 : ℝ), (2590927987/5000000000 : ℝ)] ![(10337122171831/100000000000000 : ℝ), (5787487482389/12500000000000 : ℝ), (169386632639/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419246779/2500000000 : ℝ)|^4803 ≤ (10337122171831/100000000000000 : ℝ)^3779
        have hw : |(-419246779/2500000000 : ℝ)|=(419246779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456050891/10000000000 : ℝ)|^4803 ≤ (5787487482389/12500000000000 : ℝ)^3779
        have hw : |(5456050891/10000000000 : ℝ)|=(5456050891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590927987/5000000000 : ℝ)|^4803 ≤ (169386632639/390625000000 : ℝ)^3779
        have hw : |(2590927987/5000000000 : ℝ)|=(2590927987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337995099/2500000000 : ℝ)*x 0 + (-909152683/5000000000 : ℝ)*x 1 + (5181855629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337995099/2500000000 : ℝ)^4803 ≤ (5647546180611/12500000000000 : ℝ)^3779 := by
    have hnat : (1337995099 : ℕ)^4803*12500000000000^3779 ≤ 5647546180611^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337995099 2500000000 5647546180611 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909152683/5000000000 : ℝ)^4803 ≤ (11456656250909/100000000000000 : ℝ)^3779 := by
    have hnat : (909152683 : ℕ)^4803*100000000000000^3779 ≤ 11456656250909^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909152683 5000000000 11456656250909 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181855629/10000000000 : ℝ)^4803 ≤ (43362974286239/100000000000000 : ℝ)^3779 := by
    have hnat : (5181855629 : ℕ)^4803*100000000000000^3779 ≤ 43362974286239^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181855629 10000000000 43362974286239 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337995099/2500000000 : ℝ), (-909152683/5000000000 : ℝ), (5181855629/10000000000 : ℝ)] ![(5647546180611/12500000000000 : ℝ), (11456656250909/100000000000000 : ℝ), (43362974286239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337995099/2500000000 : ℝ)|^4803 ≤ (5647546180611/12500000000000 : ℝ)^3779
        have hw : |(1337995099/2500000000 : ℝ)|=(1337995099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-909152683/5000000000 : ℝ)|^4803 ≤ (11456656250909/100000000000000 : ℝ)^3779
        have hw : |(-909152683/5000000000 : ℝ)|=(909152683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181855629/10000000000 : ℝ)|^4803 ≤ (43362974286239/100000000000000 : ℝ)^3779
        have hw : |(5181855629/10000000000 : ℝ)|=(5181855629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351980211/10000000000 : ℝ)*x 0 + (5181855843/10000000000 : ℝ)*x 1 + (-181830533/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351980211/10000000000 : ℝ)^4803 ≤ (4518036745997/10000000000000 : ℝ)^3779 := by
    have hnat : (5351980211 : ℕ)^4803*10000000000000^3779 ≤ 4518036745997^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351980211 10000000000 4518036745997 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181855843/10000000000 : ℝ)^4803 ≤ (5420372070287/12500000000000 : ℝ)^3779 := by
    have hnat : (5181855843 : ℕ)^4803*12500000000000^3779 ≤ 5420372070287^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181855843 10000000000 5420372070287 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181830533/1000000000 : ℝ)^4803 ≤ (11456655962619/100000000000000 : ℝ)^3779 := by
    have hnat : (181830533 : ℕ)^4803*100000000000000^3779 ≤ 11456655962619^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181830533 1000000000 11456655962619 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351980211/10000000000 : ℝ), (5181855843/10000000000 : ℝ), (-181830533/1000000000 : ℝ)] ![(4518036745997/10000000000000 : ℝ), (5420372070287/12500000000000 : ℝ), (11456655962619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351980211/10000000000 : ℝ)|^4803 ≤ (4518036745997/10000000000000 : ℝ)^3779
        have hw : |(5351980211/10000000000 : ℝ)|=(5351980211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181855843/10000000000 : ℝ)|^4803 ≤ (5420372070287/12500000000000 : ℝ)^3779
        have hw : |(5181855843/10000000000 : ℝ)|=(5181855843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181830533/1000000000 : ℝ)|^4803 ≤ (11456655962619/100000000000000 : ℝ)^3779
        have hw : |(-181830533/1000000000 : ℝ)|=(181830533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203571721/10000000000 : ℝ)*x 0 + (1936156519/5000000000 : ℝ)*x 1 + (4555874029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203571721/10000000000 : ℝ)^4803 ≤ (33237620209339/100000000000000 : ℝ)^3779 := by
    have hnat : (4203571721 : ℕ)^4803*100000000000000^3779 ≤ 33237620209339^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203571721 10000000000 33237620209339 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936156519/5000000000 : ℝ)^4803 ≤ (29944863455657/100000000000000 : ℝ)^3779 := by
    have hnat : (1936156519 : ℕ)^4803*100000000000000^3779 ≤ 29944863455657^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936156519 5000000000 29944863455657 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4555874029/10000000000 : ℝ)^4803 ≤ (36817516312389/100000000000000 : ℝ)^3779 := by
    have hnat : (4555874029 : ℕ)^4803*100000000000000^3779 ≤ 36817516312389^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555874029 10000000000 36817516312389 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203571721/10000000000 : ℝ), (1936156519/5000000000 : ℝ), (4555874029/10000000000 : ℝ)] ![(33237620209339/100000000000000 : ℝ), (29944863455657/100000000000000 : ℝ), (36817516312389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203571721/10000000000 : ℝ)|^4803 ≤ (33237620209339/100000000000000 : ℝ)^3779
        have hw : |(4203571721/10000000000 : ℝ)|=(4203571721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936156519/5000000000 : ℝ)|^4803 ≤ (29944863455657/100000000000000 : ℝ)^3779
        have hw : |(1936156519/5000000000 : ℝ)|=(1936156519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4555874029/10000000000 : ℝ)|^4803 ≤ (36817516312389/100000000000000 : ℝ)^3779
        have hw : |(4555874029/10000000000 : ℝ)|=(4555874029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1677055613/10000000000 : ℝ)*x 0 + (1036780571/2000000000 : ℝ)*x 1 + (136349561/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1677055613/10000000000 : ℝ)^4803 ≤ (2067531761509/20000000000000 : ℝ)^3779 := by
    have hnat : (1677055613 : ℕ)^4803*20000000000000^3779 ≤ 2067531761509^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677055613 10000000000 2067531761509 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036780571/2000000000 : ℝ)^4803 ≤ (338943353923/781250000000 : ℝ)^3779 := by
    have hnat : (1036780571 : ℕ)^4803*781250000000^3779 ≤ 338943353923^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036780571 2000000000 338943353923 781250000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136349561/250000000 : ℝ)^4803 ≤ (46277591878347/100000000000000 : ℝ)^3779 := by
    have hnat : (136349561 : ℕ)^4803*100000000000000^3779 ≤ 46277591878347^3779*250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136349561 250000000 46277591878347 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1677055613/10000000000 : ℝ), (1036780571/2000000000 : ℝ), (136349561/250000000 : ℝ)] ![(2067531761509/20000000000000 : ℝ), (338943353923/781250000000 : ℝ), (46277591878347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1677055613/10000000000 : ℝ)|^4803 ≤ (2067531761509/20000000000000 : ℝ)^3779
        have hw : |(-1677055613/10000000000 : ℝ)|=(1677055613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036780571/2000000000 : ℝ)|^4803 ≤ (338943353923/781250000000 : ℝ)^3779
        have hw : |(1036780571/2000000000 : ℝ)|=(1036780571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136349561/250000000 : ℝ)|^4803 ≤ (46277591878347/100000000000000 : ℝ)^3779
        have hw : |(136349561/250000000 : ℝ)|=(136349561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527902391/1000000000 : ℝ)*x 0 + (-1546178463/10000000000 : ℝ)*x 1 + (681747821/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527902391/1000000000 : ℝ)^4803 ≤ (11099762177361/25000000000000 : ℝ)^3779 := by
    have hnat : (527902391 : ℕ)^4803*25000000000000^3779 ≤ 11099762177361^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527902391 1000000000 11099762177361 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546178463/10000000000 : ℝ)^4803 ≤ (1165419751459/12500000000000 : ℝ)^3779 := by
    have hnat : (1546178463 : ℕ)^4803*12500000000000^3779 ≤ 1165419751459^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546178463 10000000000 1165419751459 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681747821/1250000000 : ℝ)^4803 ≤ (46277593258739/100000000000000 : ℝ)^3779 := by
    have hnat : (681747821 : ℕ)^4803*100000000000000^3779 ≤ 46277593258739^3779*1250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681747821 1250000000 46277593258739 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527902391/1000000000 : ℝ), (-1546178463/10000000000 : ℝ), (681747821/1250000000 : ℝ)] ![(11099762177361/25000000000000 : ℝ), (1165419751459/12500000000000 : ℝ), (46277593258739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527902391/1000000000 : ℝ)|^4803 ≤ (11099762177361/25000000000000 : ℝ)^3779
        have hw : |(527902391/1000000000 : ℝ)|=(527902391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1546178463/10000000000 : ℝ)|^4803 ≤ (1165419751459/12500000000000 : ℝ)^3779
        have hw : |(-1546178463/10000000000 : ℝ)|=(1546178463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681747821/1250000000 : ℝ)|^4803 ≤ (46277593258739/100000000000000 : ℝ)^3779
        have hw : |(681747821/1250000000 : ℝ)|=(681747821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_6 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211160957/400000000 : ℝ)*x 0 + (5453982499/10000000000 : ℝ)*x 1 + (-77308927/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211160957/400000000 : ℝ)^4803 ≤ (22199524434893/50000000000000 : ℝ)^3779 := by
    have hnat : (211160957 : ℕ)^4803*50000000000000^3779 ≤ 22199524434893^3779*400000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211160957 400000000 22199524434893 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453982499/10000000000 : ℝ)^4803 ≤ (46277592514621/100000000000000 : ℝ)^3779 := by
    have hnat : (5453982499 : ℕ)^4803*100000000000000^3779 ≤ 46277592514621^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453982499 10000000000 46277592514621 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77308927/500000000 : ℝ)^4803 ≤ (932335860179/10000000000000 : ℝ)^3779 := by
    have hnat : (77308927 : ℕ)^4803*10000000000000^3779 ≤ 932335860179^3779*500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77308927 500000000 932335860179 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211160957/400000000 : ℝ), (5453982499/10000000000 : ℝ), (-77308927/500000000 : ℝ)] ![(22199524434893/50000000000000 : ℝ), (46277592514621/100000000000000 : ℝ), (932335860179/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211160957/400000000 : ℝ)|^4803 ≤ (22199524434893/50000000000000 : ℝ)^3779
        have hw : |(211160957/400000000 : ℝ)|=(211160957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453982499/10000000000 : ℝ)|^4803 ≤ (46277592514621/100000000000000 : ℝ)^3779
        have hw : |(5453982499/10000000000 : ℝ)|=(5453982499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77308927/500000000 : ℝ)|^4803 ≤ (932335860179/10000000000000 : ℝ)^3779
        have hw : |(-77308927/500000000 : ℝ)|=(77308927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s4_7 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840748433/2000000000 : ℝ)*x 0 + (2275385413/5000000000 : ℝ)*x 1 + (3877470047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840748433/2000000000 : ℝ)^4803 ≤ (16619666553187/50000000000000 : ℝ)^3779 := by
    have hnat : (840748433 : ℕ)^4803*50000000000000^3779 ≤ 16619666553187^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840748433 2000000000 16619666553187 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275385413/5000000000 : ℝ)^4803 ≤ (18382554288881/50000000000000 : ℝ)^3779 := by
    have hnat : (2275385413 : ℕ)^4803*50000000000000^3779 ≤ 18382554288881^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275385413 5000000000 18382554288881 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3877470047/10000000000 : ℝ)^4803 ≤ (29995558299799/100000000000000 : ℝ)^3779 := by
    have hnat : (3877470047 : ℕ)^4803*100000000000000^3779 ≤ 29995558299799^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877470047 10000000000 29995558299799 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840748433/2000000000 : ℝ), (2275385413/5000000000 : ℝ), (3877470047/10000000000 : ℝ)] ![(16619666553187/50000000000000 : ℝ), (18382554288881/50000000000000 : ℝ), (29995558299799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840748433/2000000000 : ℝ)|^4803 ≤ (16619666553187/50000000000000 : ℝ)^3779
        have hw : |(840748433/2000000000 : ℝ)|=(840748433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2275385413/5000000000 : ℝ)|^4803 ≤ (18382554288881/50000000000000 : ℝ)^3779
        have hw : |(2275385413/5000000000 : ℝ)|=(2275385413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3877470047/10000000000 : ℝ)|^4803 ≤ (29995558299799/100000000000000 : ℝ)^3779
        have hw : |(3877470047/10000000000 : ℝ)|=(3877470047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4083/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2101/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8161/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4083/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4083/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4083/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4083/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4083/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4083/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10497/100000 : ℝ) ^ (4799/1024 : ℝ) ≤ (2583444302795717/100000000000000000000 : ℝ) := by
    have hpowers : (10497/100000 : ℝ)^4799 ≤ (2583444302795717/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10497 : ℕ)^4799*100000000000000000000^1024 ≤ 2583444302795717^1024*100000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10497 100000 2583444302795717 100000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10497/100000 : ℝ)) (X := (2583444302795717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4083/25000 : ℝ) ^ (4799/1024 : ℝ) ≤ (20506454039036817/100000000000000000000 : ℝ) := by
    have hpowers : (4083/25000 : ℝ)^4799 ≤ (20506454039036817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4083 : ℕ)^4799*100000000000000000000^1024 ≤ 20506454039036817^1024*25000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4083 25000 20506454039036817 100000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4083/25000 : ℝ)) (X := (20506454039036817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002583444302795717/50000000000000000000 : ℝ) ≤ (1000011024768523/1000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50002583444302795717/50000000000000000000 : ℝ)^1024 ≤ (1000011024768523/1000000000000000 : ℝ)^4799 := by
      have hnat : (50002583444302795717 : ℕ)^1024*1000000000000000^4799 ≤ 1000011024768523^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002583444302795717 50000000000000000000 1000011024768523 1000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000011024768523/1000000000000000 : ℝ)) (X := (50002583444302795717/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011544949170916267/50000000000000000000 : ℝ) ≤ (10000492642403817/10000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50011544949170916267/50000000000000000000 : ℝ)^1024 ≤ (10000492642403817/10000000000000000 : ℝ)^4799 := by
      have hnat : (50011544949170916267 : ℕ)^1024*10000000000000000^4799 ≤ 10000492642403817^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011544949170916267 50000000000000000000 10000492642403817 10000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000492642403817/10000000000000000 : ℝ)) (X := (50011544949170916267/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020506454039036817/50000000000000000000 : ℝ) ≤ (2500218759280601/2500000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (50020506454039036817/50000000000000000000 : ℝ)^1024 ≤ (2500218759280601/2500000000000000 : ℝ)^4799 := by
      have hnat : (50020506454039036817 : ℕ)^1024*2500000000000000^4799 ≤ 2500218759280601^4799*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020506454039036817 50000000000000000000 2500218759280601 2500000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500218759280601/2500000000000000 : ℝ)) (X := (50020506454039036817/50000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2583444302795717/100000000000000000000 : ℝ) ≤ ((4861884608376775131/4862500000000000000 : ℝ)+2*(382394718587/583500000000000 : ℝ)*(10497/100000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (4861884608376775131/4862500000000000000 : ℝ)+2*(382394718587/583500000000000 : ℝ)*(10497/100000 : ℝ)=(1000011024768523/1000000000000000 : ℝ) by norm_num, show 1+2*(2583444302795717/100000000000000000000 : ℝ)=(50002583444302795717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20506454039036817/100000000000000000000 : ℝ)+(2583444302795717/100000000000000000000 : ℝ) ≤ ((4861884608376775131/4862500000000000000 : ℝ)+(382394718587/583500000000000 : ℝ)*((4083/25000 : ℝ)+(10497/100000 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (4861884608376775131/4862500000000000000 : ℝ)+(382394718587/583500000000000 : ℝ)*((4083/25000 : ℝ)+(10497/100000 : ℝ))=(10000492642403817/10000000000000000 : ℝ) by norm_num, show 1+(20506454039036817/100000000000000000000 : ℝ)+(2583444302795717/100000000000000000000 : ℝ)=(50011544949170916267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20506454039036817/100000000000000000000 : ℝ) ≤ ((4861884608376775131/4862500000000000000 : ℝ)+2*(382394718587/583500000000000 : ℝ)*(4083/25000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (4861884608376775131/4862500000000000000 : ℝ)+2*(382394718587/583500000000000 : ℝ)*(4083/25000 : ℝ)=(2500218759280601/2500000000000000 : ℝ) by norm_num, show 1+2*(20506454039036817/100000000000000000000 : ℝ)=(50020506454039036817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4861884608376775131/4862500000000000000 : ℝ)*(X 1 0+X 2 0)+(382394718587/583500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (4083/25000 : ℝ)) (c := (4861884608376775131/4862500000000000000 : ℝ)) (alpha := (382394718587/583500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4861884608376775131/4862500000000000000 : ℝ)*(X 0 1+X 2 1)+(382394718587/583500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (4083/25000 : ℝ)) (c := (4861884608376775131/4862500000000000000 : ℝ)) (alpha := (382394718587/583500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4861884608376775131/4862500000000000000 : ℝ)*(X 0 2+X 1 2)+(382394718587/583500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (4083/25000 : ℝ)) (c := (4861884608376775131/4862500000000000000 : ℝ)) (alpha := (382394718587/583500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419246779/2500000000 : ℝ)*X 0 0+(5456050891/10000000000 : ℝ)*X 0 1+(2590927987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337995099/2500000000 : ℝ)*X 1 0+(-909152683/5000000000 : ℝ)*X 1 1+(5181855629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351980211/10000000000 : ℝ)*X 2 0+(5181855843/10000000000 : ℝ)*X 2 1+(-181830533/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203571721/10000000000 : ℝ)*X 0 0+(1936156519/5000000000 : ℝ)*X 0 1+(4555874029/10000000000 : ℝ)*X 0 2+(4203571721/10000000000 : ℝ)*X 1 0+(1936156519/5000000000 : ℝ)*X 1 1+(4555874029/10000000000 : ℝ)*X 1 2+(4203571721/10000000000 : ℝ)*X 2 0+(1936156519/5000000000 : ℝ)*X 2 1+(4555874029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1677055613/10000000000 : ℝ)*X 0 0+(1036780571/2000000000 : ℝ)*X 0 1+(136349561/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527902391/1000000000 : ℝ)*X 1 0+(-1546178463/10000000000 : ℝ)*X 1 1+(681747821/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211160957/400000000 : ℝ)*X 2 0+(5453982499/10000000000 : ℝ)*X 2 1+(-77308927/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840748433/2000000000 : ℝ)*X 0 0+(2275385413/5000000000 : ℝ)*X 0 1+(3877470047/10000000000 : ℝ)*X 0 2+(840748433/2000000000 : ℝ)*X 1 0+(2275385413/5000000000 : ℝ)*X 1 1+(3877470047/10000000000 : ℝ)*X 1 2+(840748433/2000000000 : ℝ)*X 2 0+(2275385413/5000000000 : ℝ)*X 2 1+(3877470047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (959253517309374172915929111/121562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1396823387/100000000000000 : ℝ)*(base19) + (1168772427/100000000000000 : ℝ)*(base23) + (6822711/12500000000000 : ℝ)*(lower2) + (187435941/100000000000000 : ℝ)*(upper3) + (122370731/100000000000000 : ℝ)*(upper5) + (1277502189245473/50000000000000 : ℝ)*(major0) + (1277502189245473/50000000000000 : ℝ)*(major1) + (1277502189245473/50000000000000 : ℝ)*(major2) + (1823527426624671/50000000000000 : ℝ)*(sp0) + (56985416818407/1562500000000 : ℝ)*(sp1) + (227941681526813/6250000000000 : ℝ)*(sp2) + (731466757162259/50000000000000 : ℝ)*(sp3) + (3304988023/25000000000000 : ℝ)*(sp4) + (6906421549/100000000000000 : ℝ)*(sp7) + (731470210373033/50000000000000 : ℝ)*(f.failure) + (729413614640287/20000000000000 : ℝ)*(f.sum) + (178202560765823/29175000000000000000000000000 : ℝ)*base66 + (1209826496070970889/729375000000000000000000000000000 : ℝ)*base67 + (2324867372451595889/729375000000000000000000000000000 : ℝ)*base69 + (1356916247522845889/729375000000000000000000000000000 : ℝ)*base71 + (27117779718737/7293750000000000000000000000 : ℝ)*base74 + (1903537296840904111/729375000000000000000000000000000 : ℝ)*base76 + (5856320730327154111/729375000000000000000000000000000 : ℝ)*base78 + (2422625876412220889/729375000000000000000000000000000 : ℝ)*base79 + (24403979740927/29175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (296469/62500000000000000000 : ℝ)*base90 + (296469/62500000000000000000 : ℝ)*base92 + (296469/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (630877899305040379781631383/243125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9963887/2000000000000 : ℝ)*(base19) + (273590897/50000000000000 : ℝ)*(base23) + (213257663/100000000000000 : ℝ)*(lower1) + (21979717/100000000000000 : ℝ)*(upper2) + (13593823/25000000000000 : ℝ)*(upper3) + (36061437/100000000000000 : ℝ)*(upper5) + (2593910467884431/100000000000000 : ℝ)*(major0) + (2593910467884431/100000000000000 : ℝ)*(major1) + (2593910467884431/100000000000000 : ℝ)*(major2) + (229319221/100000000000000 : ℝ)*(sp1) + (1851301820281521/50000000000000 : ℝ)*(sp4) + (370260291304947/10000000000000 : ℝ)*(sp5) + (3702603093381247/100000000000000 : ℝ)*(sp6) + (1485217208710127/100000000000000 : ℝ)*(sp7) + (1485217208710127/100000000000000 : ℝ)*(f.failure) + (1851301820281521/50000000000000 : ℝ)*(f.sum) + (51765306864289/14587500000000000000000000000 : ℝ)*base66 + (241771942068581383/1458750000000000000000000000000000 : ℝ)*base67 + (48255551407155168617/1458750000000000000000000000000000 : ℝ)*base70 + (3495536633377331383/1458750000000000000000000000000000 : ℝ)*base71 + (49999900523947/29175000000000000000000000000 : ℝ)*base73 + (8136135829233918617/1458750000000000000000000000000000 : ℝ)*base76 + (1899672500688918617/1458750000000000000000000000000000 : ℝ)*base78 + (9446532729532668617/1458750000000000000000000000000000 : ℝ)*base80 + (91622388557539/14587500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (474589/125000000000000000000 : ℝ)*base89 + (474589/125000000000000000000 : ℝ)*base91 + (474589/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1621_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4083/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2101/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1621_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1621_s5_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1676995527/10000000000 : ℝ)*x 0 + (1091202869/2000000000 : ℝ)*x 1 + (2590943419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1676995527/10000000000 : ℝ)^4803 ≤ (2584297016749/25000000000000 : ℝ)^3779 := by
    have hnat : (1676995527 : ℕ)^4803*25000000000000^3779 ≤ 2584297016749^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676995527 10000000000 2584297016749 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091202869/2000000000 : ℝ)^4803 ≤ (1446859552977/3125000000000 : ℝ)^3779 := by
    have hnat : (1091202869 : ℕ)^4803*3125000000000^3779 ≤ 1446859552977^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091202869 2000000000 1446859552977 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590943419/5000000000 : ℝ)^4803 ≤ (43363306218647/100000000000000 : ℝ)^3779 := by
    have hnat : (2590943419 : ℕ)^4803*100000000000000^3779 ≤ 43363306218647^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590943419 5000000000 43363306218647 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1676995527/10000000000 : ℝ), (1091202869/2000000000 : ℝ), (2590943419/5000000000 : ℝ)] ![(2584297016749/25000000000000 : ℝ), (1446859552977/3125000000000 : ℝ), (43363306218647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1676995527/10000000000 : ℝ)|^4803 ≤ (2584297016749/25000000000000 : ℝ)^3779
        have hw : |(-1676995527/10000000000 : ℝ)|=(1676995527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091202869/2000000000 : ℝ)|^4803 ≤ (1446859552977/3125000000000 : ℝ)^3779
        have hw : |(1091202869/2000000000 : ℝ)|=(1091202869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590943419/5000000000 : ℝ)|^4803 ≤ (43363306218647/100000000000000 : ℝ)^3779
        have hw : |(2590943419/5000000000 : ℝ)|=(2590943419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s5_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337992493/2500000000 : ℝ)*x 0 + (-1818278149/10000000000 : ℝ)*x 1 + (2590943319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337992493/2500000000 : ℝ)^4803 ≤ (9036051520561/20000000000000 : ℝ)^3779 := by
    have hnat : (1337992493 : ℕ)^4803*20000000000000^3779 ≤ 9036051520561^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337992493 2500000000 9036051520561 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1818278149/10000000000 : ℝ)^4803 ≤ (1432054787033/12500000000000 : ℝ)^3779 := by
    have hnat : (1818278149 : ℕ)^4803*12500000000000^3779 ≤ 1432054787033^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818278149 10000000000 1432054787033 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590943319/5000000000 : ℝ)^4803 ≤ (43363304091487/100000000000000 : ℝ)^3779 := by
    have hnat : (2590943319 : ℕ)^4803*100000000000000^3779 ≤ 43363304091487^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590943319 5000000000 43363304091487 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337992493/2500000000 : ℝ), (-1818278149/10000000000 : ℝ), (2590943319/5000000000 : ℝ)] ![(9036051520561/20000000000000 : ℝ), (1432054787033/12500000000000 : ℝ), (43363304091487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337992493/2500000000 : ℝ)|^4803 ≤ (9036051520561/20000000000000 : ℝ)^3779
        have hw : |(1337992493/2500000000 : ℝ)|=(1337992493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1818278149/10000000000 : ℝ)|^4803 ≤ (1432054787033/12500000000000 : ℝ)^3779
        have hw : |(-1818278149/10000000000 : ℝ)|=(1818278149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590943319/5000000000 : ℝ)|^4803 ≤ (43363304091487/100000000000000 : ℝ)^3779
        have hw : |(2590943319/5000000000 : ℝ)|=(2590943319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s5_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351970123/10000000000 : ℝ)*x 0 + (518188647/1000000000 : ℝ)*x 1 + (-181827817/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351970123/10000000000 : ℝ)^4803 ≤ (45180259222927/100000000000000 : ℝ)^3779 := by
    have hnat : (5351970123 : ℕ)^4803*100000000000000^3779 ≤ 45180259222927^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351970123 10000000000 45180259222927 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518188647/1000000000 : ℝ)^4803 ≤ (1355103197021/3125000000000 : ℝ)^3779 := by
    have hnat : (518188647 : ℕ)^4803*3125000000000^3779 ≤ 1355103197021^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518188647 1000000000 1355103197021 3125000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181827817/1000000000 : ℝ)^4803 ≤ (716027404027/6250000000000 : ℝ)^3779 := by
    have hnat : (181827817 : ℕ)^4803*6250000000000^3779 ≤ 716027404027^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181827817 1000000000 716027404027 6250000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351970123/10000000000 : ℝ), (518188647/1000000000 : ℝ), (-181827817/1000000000 : ℝ)] ![(45180259222927/100000000000000 : ℝ), (1355103197021/3125000000000 : ℝ), (716027404027/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351970123/10000000000 : ℝ)|^4803 ≤ (45180259222927/100000000000000 : ℝ)^3779
        have hw : |(5351970123/10000000000 : ℝ)|=(5351970123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518188647/1000000000 : ℝ)|^4803 ≤ (1355103197021/3125000000000 : ℝ)^3779
        have hw : |(518188647/1000000000 : ℝ)|=(518188647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181827817/1000000000 : ℝ)|^4803 ≤ (716027404027/6250000000000 : ℝ)^3779
        have hw : |(-181827817/1000000000 : ℝ)|=(181827817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s5_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2101788227/5000000000 : ℝ)*x 0 + (1936198607/5000000000 : ℝ)*x 1 + (91115777/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101788227/5000000000 : ℝ)^4803 ≤ (1329506710957/4000000000000 : ℝ)^3779 := by
    have hnat : (2101788227 : ℕ)^4803*4000000000000^3779 ≤ 1329506710957^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101788227 5000000000 1329506710957 4000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936198607/5000000000 : ℝ)^4803 ≤ (29945690782541/100000000000000 : ℝ)^3779 := by
    have hnat : (1936198607 : ℕ)^4803*100000000000000^3779 ≤ 29945690782541^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936198607 5000000000 29945690782541 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91115777/200000000 : ℝ)^4803 ≤ (460208017869/1250000000000 : ℝ)^3779 := by
    have hnat : (91115777 : ℕ)^4803*1250000000000^3779 ≤ 460208017869^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91115777 200000000 460208017869 1250000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101788227/5000000000 : ℝ), (1936198607/5000000000 : ℝ), (91115777/200000000 : ℝ)] ![(1329506710957/4000000000000 : ℝ), (29945690782541/100000000000000 : ℝ), (460208017869/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101788227/5000000000 : ℝ)|^4803 ≤ (1329506710957/4000000000000 : ℝ)^3779
        have hw : |(2101788227/5000000000 : ℝ)|=(2101788227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936198607/5000000000 : ℝ)|^4803 ≤ (29945690782541/100000000000000 : ℝ)^3779
        have hw : |(1936198607/5000000000 : ℝ)|=(1936198607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91115777/200000000 : ℝ)|^4803 ≤ (460208017869/1250000000000 : ℝ)^3779
        have hw : |(91115777/200000000 : ℝ)|=(91115777/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s5_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-838530351/5000000000 : ℝ)*x 0 + (1036786247/2000000000 : ℝ)*x 1 + (21815803/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838530351/5000000000 : ℝ)^4803 ≤ (10337698677253/100000000000000 : ℝ)^3779 := by
    have hnat : (838530351 : ℕ)^4803*100000000000000^3779 ≤ 10337698677253^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838530351 5000000000 10337698677253 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036786247/2000000000 : ℝ)^4803 ≤ (8677010235637/20000000000000 : ℝ)^3779 := by
    have hnat : (1036786247 : ℕ)^4803*20000000000000^3779 ≤ 8677010235637^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036786247 2000000000 8677010235637 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21815803/40000000 : ℝ)^4803 ≤ (23138625061779/50000000000000 : ℝ)^3779 := by
    have hnat : (21815803 : ℕ)^4803*50000000000000^3779 ≤ 23138625061779^3779*40000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21815803 40000000 23138625061779 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-838530351/5000000000 : ℝ), (1036786247/2000000000 : ℝ), (21815803/40000000 : ℝ)] ![(10337698677253/100000000000000 : ℝ), (8677010235637/20000000000000 : ℝ), (23138625061779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-838530351/5000000000 : ℝ)|^4803 ≤ (10337698677253/100000000000000 : ℝ)^3779
        have hw : |(-838530351/5000000000 : ℝ)|=(838530351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036786247/2000000000 : ℝ)|^4803 ≤ (8677010235637/20000000000000 : ℝ)^3779
        have hw : |(1036786247/2000000000 : ℝ)|=(1036786247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21815803/40000000 : ℝ)|^4803 ≤ (23138625061779/50000000000000 : ℝ)^3779
        have hw : |(21815803/40000000 : ℝ)|=(21815803/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_s5_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4203752969/10000000000 : ℝ)*x 0 + (2275342793/5000000000 : ℝ)*x 1 + (3877548023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203752969/10000000000 : ℝ)^4803 ≤ (16619720841539/50000000000000 : ℝ)^3779 := by
    have hnat : (4203752969 : ℕ)^4803*50000000000000^3779 ≤ 16619720841539^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203752969 10000000000 16619720841539 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275342793/5000000000 : ℝ)^4803 ≤ (36764233334207/100000000000000 : ℝ)^3779 := by
    have hnat : (2275342793 : ℕ)^4803*100000000000000^3779 ≤ 36764233334207^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275342793 5000000000 36764233334207 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3877548023/10000000000 : ℝ)^4803 ≤ (29996324966021/100000000000000 : ℝ)^3779 := by
    have hnat : (3877548023 : ℕ)^4803*100000000000000^3779 ≤ 29996324966021^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877548023 10000000000 29996324966021 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203752969/10000000000 : ℝ), (2275342793/5000000000 : ℝ), (3877548023/10000000000 : ℝ)] ![(16619720841539/50000000000000 : ℝ), (36764233334207/100000000000000 : ℝ), (29996324966021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203752969/10000000000 : ℝ)|^4803 ≤ (16619720841539/50000000000000 : ℝ)^3779
        have hw : |(4203752969/10000000000 : ℝ)|=(4203752969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2275342793/5000000000 : ℝ)|^4803 ≤ (36764233334207/100000000000000 : ℝ)^3779
        have hw : |(2275342793/5000000000 : ℝ)|=(2275342793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3877548023/10000000000 : ℝ)|^4803 ≤ (29996324966021/100000000000000 : ℝ)^3779
        have hw : |(3877548023/10000000000 : ℝ)|=(3877548023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2101/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5253/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8161/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2101/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2101/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2101/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2101/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2101/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2101/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2101/20000 : ℝ) ^ (4799/1024 : ℝ) ≤ (1296342287519359/50000000000000000000 : ℝ) := by
    have hpowers : (2101/20000 : ℝ)^4799 ≤ (1296342287519359/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2101 : ℕ)^4799*50000000000000000000^1024 ≤ 1296342287519359^1024*20000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2101 20000 1296342287519359 50000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2101/20000 : ℝ)) (X := (1296342287519359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8161/50000 : ℝ) ^ (4799/1024 : ℝ) ≤ (10223838220814081/50000000000000000000 : ℝ) := by
    have hpowers : (8161/50000 : ℝ)^4799 ≤ (10223838220814081/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8161 : ℕ)^4799*50000000000000000000^1024 ≤ 10223838220814081^1024*50000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8161 50000 10223838220814081 50000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8161/50000 : ℝ)) (X := (10223838220814081/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001296342287519359/25000000000000000000 : ℝ) ≤ (9765733048831/9765625000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (25001296342287519359/25000000000000000000 : ℝ)^1024 ≤ (9765733048831/9765625000000 : ℝ)^4799 := by
      have hnat : (25001296342287519359 : ℕ)^1024*9765625000000^4799 ≤ 9765733048831^4799*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001296342287519359 25000000000000000000 9765733048831 9765625000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9765733048831/9765625000000 : ℝ)) (X := (25001296342287519359/25000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (78143000282044271/78125000000000000 : ℝ) ≤ (400019663423163/400000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (78143000282044271/78125000000000000 : ℝ)^1024 ≤ (400019663423163/400000000000000 : ℝ)^4799 := by
      have hnat : (78143000282044271 : ℕ)^1024*400000000000000^4799 ≤ 400019663423163^4799*78125000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78143000282044271 78125000000000000 400019663423163 400000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400019663423163/400000000000000 : ℝ)) (X := (78143000282044271/78125000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010223838220814081/25000000000000000000 : ℝ) ≤ (5000436264577603/5000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (25010223838220814081/25000000000000000000 : ℝ)^1024 ≤ (5000436264577603/5000000000000000 : ℝ)^4799 := by
      have hnat : (25010223838220814081 : ℕ)^1024*5000000000000000^4799 ≤ 5000436264577603^4799*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010223838220814081 25000000000000000000 5000436264577603 5000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000436264577603/5000000000000000 : ℝ)) (X := (25010223838220814081/25000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1296342287519359/50000000000000000000 : ℝ) ≤ ((29081319989998306469/29085000000000000000 : ℝ)+2*(380943576131/581700000000000 : ℝ)*(2101/20000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (29081319989998306469/29085000000000000000 : ℝ)+2*(380943576131/581700000000000 : ℝ)*(2101/20000 : ℝ)=(9765733048831/9765625000000 : ℝ) by norm_num, show 1+2*(1296342287519359/50000000000000000000 : ℝ)=(25001296342287519359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10223838220814081/50000000000000000000 : ℝ)+(1296342287519359/50000000000000000000 : ℝ) ≤ ((29081319989998306469/29085000000000000000 : ℝ)+(380943576131/581700000000000 : ℝ)*((8161/50000 : ℝ)+(2101/20000 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (29081319989998306469/29085000000000000000 : ℝ)+(380943576131/581700000000000 : ℝ)*((8161/50000 : ℝ)+(2101/20000 : ℝ))=(400019663423163/400000000000000 : ℝ) by norm_num, show 1+(10223838220814081/50000000000000000000 : ℝ)+(1296342287519359/50000000000000000000 : ℝ)=(78143000282044271/78125000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10223838220814081/50000000000000000000 : ℝ) ≤ ((29081319989998306469/29085000000000000000 : ℝ)+2*(380943576131/581700000000000 : ℝ)*(8161/50000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (29081319989998306469/29085000000000000000 : ℝ)+2*(380943576131/581700000000000 : ℝ)*(8161/50000 : ℝ)=(5000436264577603/5000000000000000 : ℝ) by norm_num, show 1+2*(10223838220814081/50000000000000000000 : ℝ)=(25010223838220814081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29081319989998306469/29085000000000000000 : ℝ)*(X 1 0+X 2 0)+(380943576131/581700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (2101/20000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (29081319989998306469/29085000000000000000 : ℝ)) (alpha := (380943576131/581700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29081319989998306469/29085000000000000000 : ℝ)*(X 0 1+X 2 1)+(380943576131/581700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (2101/20000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (29081319989998306469/29085000000000000000 : ℝ)) (alpha := (380943576131/581700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29081319989998306469/29085000000000000000 : ℝ)*(X 0 2+X 1 2)+(380943576131/581700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (2101/20000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (29081319989998306469/29085000000000000000 : ℝ)) (alpha := (380943576131/581700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1676995527/10000000000 : ℝ)*X 0 0+(1091202869/2000000000 : ℝ)*X 0 1+(2590943419/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337992493/2500000000 : ℝ)*X 1 0+(-1818278149/10000000000 : ℝ)*X 1 1+(2590943319/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351970123/10000000000 : ℝ)*X 2 0+(518188647/1000000000 : ℝ)*X 2 1+(-181827817/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101788227/5000000000 : ℝ)*X 0 0+(1936198607/5000000000 : ℝ)*X 0 1+(91115777/200000000 : ℝ)*X 0 2+(2101788227/5000000000 : ℝ)*X 1 0+(1936198607/5000000000 : ℝ)*X 1 1+(91115777/200000000 : ℝ)*X 1 2+(2101788227/5000000000 : ℝ)*X 2 0+(1936198607/5000000000 : ℝ)*X 2 1+(91115777/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-838530351/5000000000 : ℝ)*X 0 0+(1036786247/2000000000 : ℝ)*X 0 1+(21815803/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4203752969/10000000000 : ℝ)*X 0 0+(2275342793/5000000000 : ℝ)*X 0 1+(3877548023/10000000000 : ℝ)*X 0 2+(4203752969/10000000000 : ℝ)*X 1 0+(2275342793/5000000000 : ℝ)*X 1 1+(3877548023/10000000000 : ℝ)*X 1 2+(4203752969/10000000000 : ℝ)*X 2 0+(2275342793/5000000000 : ℝ)*X 2 1+(3877548023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (574260243491829898907417541/121187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616475649/100000000000000 : ℝ)*(base19) + (631600111/100000000000000 : ℝ)*(base23) + (46989399/100000000000000 : ℝ)*(lower2) + (24237987/20000000000000 : ℝ)*(upper3) + (56689431/100000000000000 : ℝ)*(upper5) + (1277809444295211/50000000000000 : ℝ)*(major0) + (1277809444295211/50000000000000 : ℝ)*(major1) + (1277809444295211/50000000000000 : ℝ)*(major2) + (3647941561925551/100000000000000 : ℝ)*(sp0) + (455993090846433/12500000000000 : ℝ)*(sp1) + (1823972355823501/50000000000000 : ℝ)*(sp2) + (91455661356873/6250000000000 : ℝ)*(sp3) + (3781321561/100000000000000 : ℝ)*(sp4) + (211783763/12500000000000 : ℝ)*(sp5) + (182911534497509/12500000000000 : ℝ)*(f.failure) + (455993167905889/12500000000000 : ℝ)*(f.sum) + (23593482594039/9695000000000000000000000000 : ℝ)*base65 + (1930950324552856653/484750000000000000000000000000000 : ℝ)*base67 + (5148215398026356653/484750000000000000000000000000000 : ℝ)*base69 + (1744721866560356653/484750000000000000000000000000000 : ℝ)*base71 + (3132397788447/4847500000000000000000000000 : ℝ)*base73 + (625825835927643347/484750000000000000000000000000000 : ℝ)*base76 + (4172329391689856653/484750000000000000000000000000000 : ℝ)*base77 + (7091125703705356653/484750000000000000000000000000000 : ℝ)*base79 + (14455649324477/4847500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (57037/15625000000000000000 : ℝ)*base90 + (57037/15625000000000000000 : ℝ)*base92 + (57037/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1621_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2101/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1621_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1621_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1621_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1621_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1621_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1299/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1621_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

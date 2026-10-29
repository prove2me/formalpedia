-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1359_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:34.297387+00:00
-- url     : https://prove2.me/submissions/150c3bda-b85a-4f9a-9b62-d293ddceb4db

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
theorem support_rectangle_w1359_s6_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014685147/5000000000 : ℝ)*x 0 + (2705920433/5000000000 : ℝ)*x 1 + (1049021589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014685147/5000000000 : ℝ)^4319 ≤ (1236252743879/10000000000000 : ℝ)^3295 := by
    have hnat : (1014685147 : ℕ)^4319*10000000000000^3295 ≤ 1236252743879^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014685147 5000000000 1236252743879 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705920433/5000000000 : ℝ)^4319 ≤ (1788692147339/4000000000000 : ℝ)^3295 := by
    have hnat : (2705920433 : ℕ)^4319*4000000000000^3295 ≤ 1788692147339^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705920433 5000000000 1788692147339 4000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049021589/2000000000 : ℝ)^4319 ≤ (21460084428157/50000000000000 : ℝ)^3295 := by
    have hnat : (1049021589 : ℕ)^4319*50000000000000^3295 ≤ 21460084428157^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049021589 2000000000 21460084428157 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014685147/5000000000 : ℝ), (2705920433/5000000000 : ℝ), (1049021589/2000000000 : ℝ)] ![(1236252743879/10000000000000 : ℝ), (1788692147339/4000000000000 : ℝ), (21460084428157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014685147/5000000000 : ℝ)|^4319 ≤ (1236252743879/10000000000000 : ℝ)^3295
        have hw : |(-1014685147/5000000000 : ℝ)|=(1014685147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705920433/5000000000 : ℝ)|^4319 ≤ (1788692147339/4000000000000 : ℝ)^3295
        have hw : |(2705920433/5000000000 : ℝ)|=(2705920433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049021589/2000000000 : ℝ)|^4319 ≤ (21460084428157/50000000000000 : ℝ)^3295
        have hw : |(1049021589/2000000000 : ℝ)|=(1049021589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348701687/10000000000 : ℝ)*x 0 + (-211430873/1000000000 : ℝ)*x 1 + (5245107989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348701687/10000000000 : ℝ)^4319 ≤ (11008675582533/25000000000000 : ℝ)^3295 := by
    have hnat : (5348701687 : ℕ)^4319*25000000000000^3295 ≤ 11008675582533^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348701687 10000000000 11008675582533 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211430873/1000000000 : ℝ)^4319 ≤ (13045128332459/100000000000000 : ℝ)^3295 := by
    have hnat : (211430873 : ℕ)^4319*100000000000000^3295 ≤ 13045128332459^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211430873 1000000000 13045128332459 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245107989/10000000000 : ℝ)^4319 ≤ (8584033865651/20000000000000 : ℝ)^3295 := by
    have hnat : (5245107989 : ℕ)^4319*20000000000000^3295 ≤ 8584033865651^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245107989 10000000000 8584033865651 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348701687/10000000000 : ℝ), (-211430873/1000000000 : ℝ), (5245107989/10000000000 : ℝ)] ![(11008675582533/25000000000000 : ℝ), (13045128332459/100000000000000 : ℝ), (8584033865651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348701687/10000000000 : ℝ)|^4319 ≤ (11008675582533/25000000000000 : ℝ)^3295
        have hw : |(5348701687/10000000000 : ℝ)|=(5348701687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211430873/1000000000 : ℝ)|^4319 ≤ (13045128332459/100000000000000 : ℝ)^3295
        have hw : |(-211430873/1000000000 : ℝ)|=(211430873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245107989/10000000000 : ℝ)|^4319 ≤ (8584033865651/20000000000000 : ℝ)^3295
        have hw : |(5245107989/10000000000 : ℝ)|=(5245107989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674350873/5000000000 : ℝ)*x 0 + (5245107937/10000000000 : ℝ)*x 1 + (-2114308719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674350873/5000000000 : ℝ)^4319 ≤ (2201735148341/5000000000000 : ℝ)^3295 := by
    have hnat : (2674350873 : ℕ)^4319*5000000000000^3295 ≤ 2201735148341^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674350873 5000000000 2201735148341 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245107937/10000000000 : ℝ)^4319 ≤ (42920168770507/100000000000000 : ℝ)^3295 := by
    have hnat : (5245107937 : ℕ)^4319*100000000000000^3295 ≤ 42920168770507^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245107937 10000000000 42920168770507 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114308719/10000000000 : ℝ)^4319 ≤ (6522564121749/50000000000000 : ℝ)^3295 := by
    have hnat : (2114308719 : ℕ)^4319*50000000000000^3295 ≤ 6522564121749^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114308719 10000000000 6522564121749 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674350873/5000000000 : ℝ), (5245107937/10000000000 : ℝ), (-2114308719/10000000000 : ℝ)] ![(2201735148341/5000000000000 : ℝ), (42920168770507/100000000000000 : ℝ), (6522564121749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674350873/5000000000 : ℝ)|^4319 ≤ (2201735148341/5000000000000 : ℝ)^3295
        have hw : |(2674350873/5000000000 : ℝ)|=(2674350873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245107937/10000000000 : ℝ)|^4319 ≤ (42920168770507/100000000000000 : ℝ)^3295
        have hw : |(5245107937/10000000000 : ℝ)|=(5245107937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114308719/10000000000 : ℝ)|^4319 ≤ (6522564121749/50000000000000 : ℝ)^3295
        have hw : |(-2114308719/10000000000 : ℝ)|=(2114308719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322192563/10000000000 : ℝ)*x 0 + (1037442939/2500000000 : ℝ)*x 1 + (4501241191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322192563/10000000000 : ℝ)^4319 ≤ (16651772244709/50000000000000 : ℝ)^3295 := by
    have hnat : (4322192563 : ℕ)^4319*50000000000000^3295 ≤ 16651772244709^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322192563 10000000000 16651772244709 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037442939/2500000000 : ℝ)^4319 ≤ (31573018547951/100000000000000 : ℝ)^3295 := by
    have hnat : (1037442939 : ℕ)^4319*100000000000000^3295 ≤ 31573018547951^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037442939 2500000000 31573018547951 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501241191/10000000000 : ℝ)^4319 ≤ (7024687390253/20000000000000 : ℝ)^3295 := by
    have hnat : (4501241191 : ℕ)^4319*20000000000000^3295 ≤ 7024687390253^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501241191 10000000000 7024687390253 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322192563/10000000000 : ℝ), (1037442939/2500000000 : ℝ), (4501241191/10000000000 : ℝ)] ![(16651772244709/50000000000000 : ℝ), (31573018547951/100000000000000 : ℝ), (7024687390253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322192563/10000000000 : ℝ)|^4319 ≤ (16651772244709/50000000000000 : ℝ)^3295
        have hw : |(4322192563/10000000000 : ℝ)|=(4322192563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037442939/2500000000 : ℝ)|^4319 ≤ (31573018547951/100000000000000 : ℝ)^3295
        have hw : |(1037442939/2500000000 : ℝ)|=(1037442939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501241191/10000000000 : ℝ)|^4319 ≤ (7024687390253/20000000000000 : ℝ)^3295
        have hw : |(4501241191/10000000000 : ℝ)|=(4501241191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-202938231/1000000000 : ℝ)*x 0 + (5245705749/10000000000 : ℝ)*x 1 + (5411239969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202938231/1000000000 : ℝ)^4319 ≤ (12362623386381/100000000000000 : ℝ)^3295 := by
    have hnat : (202938231 : ℕ)^4319*100000000000000^3295 ≤ 12362623386381^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202938231 1000000000 12362623386381 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245705749/10000000000 : ℝ)^4319 ≤ (21463290485521/50000000000000 : ℝ)^3295 := by
    have hnat : (5245705749 : ℕ)^4319*50000000000000^3295 ≤ 21463290485521^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245705749 10000000000 21463290485521 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411239969/10000000000 : ℝ)^4319 ≤ (8942159126581/20000000000000 : ℝ)^3295 := by
    have hnat : (5411239969 : ℕ)^4319*20000000000000^3295 ≤ 8942159126581^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411239969 10000000000 8942159126581 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202938231/1000000000 : ℝ), (5245705749/10000000000 : ℝ), (5411239969/10000000000 : ℝ)] ![(12362623386381/100000000000000 : ℝ), (21463290485521/50000000000000 : ℝ), (8942159126581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202938231/1000000000 : ℝ)|^4319 ≤ (12362623386381/100000000000000 : ℝ)^3295
        have hw : |(-202938231/1000000000 : ℝ)|=(202938231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245705749/10000000000 : ℝ)|^4319 ≤ (21463290485521/50000000000000 : ℝ)^3295
        have hw : |(5245705749/10000000000 : ℝ)|=(5245705749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411239969/10000000000 : ℝ)|^4319 ≤ (8942159126581/20000000000000 : ℝ)^3295
        have hw : |(5411239969/10000000000 : ℝ)|=(5411239969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305672061/10000000000 : ℝ)*x 0 + (-1948176727/10000000000 : ℝ)*x 1 + (5411239969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305672061/10000000000 : ℝ)^4319 ≤ (43570937512123/100000000000000 : ℝ)^3295 := by
    have hnat : (5305672061 : ℕ)^4319*100000000000000^3295 ≤ 43570937512123^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305672061 10000000000 43570937512123 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948176727/10000000000 : ℝ)^4319 ≤ (11718266839817/100000000000000 : ℝ)^3295 := by
    have hnat : (1948176727 : ℕ)^4319*100000000000000^3295 ≤ 11718266839817^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948176727 10000000000 11718266839817 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411239969/10000000000 : ℝ)^4319 ≤ (8942159126581/20000000000000 : ℝ)^3295 := by
    have hnat : (5411239969 : ℕ)^4319*20000000000000^3295 ≤ 8942159126581^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411239969 10000000000 8942159126581 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305672061/10000000000 : ℝ), (-1948176727/10000000000 : ℝ), (5411239969/10000000000 : ℝ)] ![(43570937512123/100000000000000 : ℝ), (11718266839817/100000000000000 : ℝ), (8942159126581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305672061/10000000000 : ℝ)|^4319 ≤ (43570937512123/100000000000000 : ℝ)^3295
        have hw : |(5305672061/10000000000 : ℝ)|=(5305672061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948176727/10000000000 : ℝ)|^4319 ≤ (11718266839817/100000000000000 : ℝ)^3295
        have hw : |(-1948176727/10000000000 : ℝ)|=(1948176727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411239969/10000000000 : ℝ)|^4319 ≤ (8942159126581/20000000000000 : ℝ)^3295
        have hw : |(5411239969/10000000000 : ℝ)|=(5411239969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305672061/10000000000 : ℝ)*x 0 + (5411239969/10000000000 : ℝ)*x 1 + (-1948176727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305672061/10000000000 : ℝ)^4319 ≤ (43570937512123/100000000000000 : ℝ)^3295 := by
    have hnat : (5305672061 : ℕ)^4319*100000000000000^3295 ≤ 43570937512123^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305672061 10000000000 43570937512123 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411239969/10000000000 : ℝ)^4319 ≤ (8942159126581/20000000000000 : ℝ)^3295 := by
    have hnat : (5411239969 : ℕ)^4319*20000000000000^3295 ≤ 8942159126581^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411239969 10000000000 8942159126581 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948176727/10000000000 : ℝ)^4319 ≤ (11718266839817/100000000000000 : ℝ)^3295 := by
    have hnat : (1948176727 : ℕ)^4319*100000000000000^3295 ≤ 11718266839817^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948176727 10000000000 11718266839817 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305672061/10000000000 : ℝ), (5411239969/10000000000 : ℝ), (-1948176727/10000000000 : ℝ)] ![(43570937512123/100000000000000 : ℝ), (8942159126581/20000000000000 : ℝ), (11718266839817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305672061/10000000000 : ℝ)|^4319 ≤ (43570937512123/100000000000000 : ℝ)^3295
        have hw : |(5305672061/10000000000 : ℝ)|=(5305672061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411239969/10000000000 : ℝ)|^4319 ≤ (8942159126581/20000000000000 : ℝ)^3295
        have hw : |(5411239969/10000000000 : ℝ)|=(5411239969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948176727/10000000000 : ℝ)|^4319 ≤ (11718266839817/100000000000000 : ℝ)^3295
        have hw : |(-1948176727/10000000000 : ℝ)|=(1948176727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s6_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322217997/10000000000 : ℝ)*x 0 + (2249990429/5000000000 : ℝ)*x 1 + (4151038463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322217997/10000000000 : ℝ)^4319 ≤ (33303801368769/100000000000000 : ℝ)^3295 := by
    have hnat : (4322217997 : ℕ)^4319*100000000000000^3295 ≤ 33303801368769^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322217997 10000000000 33303801368769 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249990429/5000000000 : ℝ)^4319 ≤ (17555273386579/50000000000000 : ℝ)^3295 := by
    have hnat : (2249990429 : ℕ)^4319*50000000000000^3295 ≤ 17555273386579^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249990429 5000000000 17555273386579 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4151038463/10000000000 : ℝ)^4319 ≤ (3948206479677/12500000000000 : ℝ)^3295 := by
    have hnat : (4151038463 : ℕ)^4319*12500000000000^3295 ≤ 3948206479677^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151038463 10000000000 3948206479677 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322217997/10000000000 : ℝ), (2249990429/5000000000 : ℝ), (4151038463/10000000000 : ℝ)] ![(33303801368769/100000000000000 : ℝ), (17555273386579/50000000000000 : ℝ), (3948206479677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322217997/10000000000 : ℝ)|^4319 ≤ (33303801368769/100000000000000 : ℝ)^3295
        have hw : |(4322217997/10000000000 : ℝ)|=(4322217997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249990429/5000000000 : ℝ)|^4319 ≤ (17555273386579/50000000000000 : ℝ)^3295
        have hw : |(2249990429/5000000000 : ℝ)|=(2249990429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4151038463/10000000000 : ℝ)|^4319 ≤ (3948206479677/12500000000000 : ℝ)^3295
        have hw : |(4151038463/10000000000 : ℝ)|=(4151038463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2797/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7359/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5591/50000 : ℝ) ^ (2159/512 : ℝ) ≤ (972299248427189/10000000000000000000 : ℝ) := by
    have hpowers : (5591/50000 : ℝ)^2159 ≤ (972299248427189/10000000000000000000 : ℝ)^512 := by
      have hnat : (5591 : ℕ)^2159*10000000000000000000^512 ≤ 972299248427189^512*50000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5591 50000 972299248427189 10000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5591/50000 : ℝ)) (X := (972299248427189/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (2159/512 : ℝ) ≤ (15517730595917301/50000000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^2159 ≤ (15517730595917301/50000000000000000000 : ℝ)^512 := by
      have hnat : (589 : ℕ)^2159*50000000000000000000^512 ≤ 15517730595917301^512*4000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 15517730595917301 50000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (15517730595917301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000972299248427189/5000000000000000000 : ℝ) ≤ (2000092224232559/2000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (5000972299248427189/5000000000000000000 : ℝ)^512 ≤ (2000092224232559/2000000000000000 : ℝ)^2159 := by
      have hnat : (5000972299248427189 : ℕ)^512*2000000000000000^2159 ≤ 2000092224232559^2159*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000972299248427189 5000000000000000000 2000092224232559 2000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092224232559/2000000000000000 : ℝ)) (X := (5000972299248427189/5000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010189613419026623/25000000000000000000 : ℝ) ≤ (10000966423566187/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (25010189613419026623/25000000000000000000 : ℝ)^512 ≤ (10000966423566187/10000000000000000 : ℝ)^2159 := by
      have hnat : (25010189613419026623 : ℕ)^512*10000000000000000^2159 ≤ 10000966423566187^2159*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010189613419026623 25000000000000000000 10000966423566187 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000966423566187/10000000000000000 : ℝ)) (X := (25010189613419026623/25000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015517730595917301/25000000000000000000 : ℝ) ≤ (10001471725969579/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (25015517730595917301/25000000000000000000 : ℝ)^512 ≤ (10001471725969579/10000000000000000 : ℝ)^2159 := by
      have hnat : (25015517730595917301 : ℕ)^512*10000000000000000^2159 ≤ 10001471725969579^2159*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015517730595917301 25000000000000000000 10001471725969579 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001471725969579/10000000000000000 : ℝ)) (X := (25015517730595917301/25000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(972299248427189/10000000000000000000 : ℝ) ≤ ((11806777723110107999/11810000000000000000 : ℝ)+2*(2631783351/1845312500000 : ℝ)*(5591/50000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (11806777723110107999/11810000000000000000 : ℝ)+2*(2631783351/1845312500000 : ℝ)*(5591/50000 : ℝ)=(2000092224232559/2000000000000000 : ℝ) by norm_num, show 1+2*(972299248427189/10000000000000000000 : ℝ)=(5000972299248427189/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15517730595917301/50000000000000000000 : ℝ)+(972299248427189/10000000000000000000 : ℝ) ≤ ((11806777723110107999/11810000000000000000 : ℝ)+(2631783351/1845312500000 : ℝ)*((589/4000 : ℝ)+(5591/50000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (11806777723110107999/11810000000000000000 : ℝ)+(2631783351/1845312500000 : ℝ)*((589/4000 : ℝ)+(5591/50000 : ℝ))=(10000966423566187/10000000000000000 : ℝ) by norm_num, show 1+(15517730595917301/50000000000000000000 : ℝ)+(972299248427189/10000000000000000000 : ℝ)=(25010189613419026623/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15517730595917301/50000000000000000000 : ℝ) ≤ ((11806777723110107999/11810000000000000000 : ℝ)+2*(2631783351/1845312500000 : ℝ)*(589/4000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (11806777723110107999/11810000000000000000 : ℝ)+2*(2631783351/1845312500000 : ℝ)*(589/4000 : ℝ)=(10001471725969579/10000000000000000 : ℝ) by norm_num, show 1+2*(15517730595917301/50000000000000000000 : ℝ)=(25015517730595917301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11806777723110107999/11810000000000000000 : ℝ)*(X 1 0+X 2 0)+(2631783351/1845312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (11806777723110107999/11810000000000000000 : ℝ)) (alpha := (2631783351/1845312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11806777723110107999/11810000000000000000 : ℝ)*(X 0 1+X 2 1)+(2631783351/1845312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (11806777723110107999/11810000000000000000 : ℝ)) (alpha := (2631783351/1845312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11806777723110107999/11810000000000000000 : ℝ)*(X 0 2+X 1 2)+(2631783351/1845312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (11806777723110107999/11810000000000000000 : ℝ)) (alpha := (2631783351/1845312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1014685147/5000000000 : ℝ)*X 0 0+(2705920433/5000000000 : ℝ)*X 0 1+(1049021589/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348701687/10000000000 : ℝ)*X 1 0+(-211430873/1000000000 : ℝ)*X 1 1+(5245107989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674350873/5000000000 : ℝ)*X 2 0+(5245107937/10000000000 : ℝ)*X 2 1+(-2114308719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322192563/10000000000 : ℝ)*X 0 0+(1037442939/2500000000 : ℝ)*X 0 1+(4501241191/10000000000 : ℝ)*X 0 2+(4322192563/10000000000 : ℝ)*X 1 0+(1037442939/2500000000 : ℝ)*X 1 1+(4501241191/10000000000 : ℝ)*X 1 2+(4322192563/10000000000 : ℝ)*X 2 0+(1037442939/2500000000 : ℝ)*X 2 1+(4501241191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-202938231/1000000000 : ℝ)*X 0 0+(5245705749/10000000000 : ℝ)*X 0 1+(5411239969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305672061/10000000000 : ℝ)*X 1 0+(-1948176727/10000000000 : ℝ)*X 1 1+(5411239969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305672061/10000000000 : ℝ)*X 2 0+(5411239969/10000000000 : ℝ)*X 2 1+(-1948176727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322217997/10000000000 : ℝ)*X 0 0+(2249990429/5000000000 : ℝ)*X 0 1+(4151038463/10000000000 : ℝ)*X 0 2+(4322217997/10000000000 : ℝ)*X 1 0+(2249990429/5000000000 : ℝ)*X 1 1+(4151038463/10000000000 : ℝ)*X 1 2+(4322217997/10000000000 : ℝ)*X 2 0+(2249990429/5000000000 : ℝ)*X 2 1+(4151038463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4378528711249954717694279541/590500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (626068499/50000000000000 : ℝ)*(base19) + (127991657/10000000000000 : ℝ)*(base23) + (5131951/25000000000000 : ℝ)*(lower2) + (130967103/100000000000000 : ℝ)*(upper3) + (63599827/50000000000000 : ℝ)*(upper5) + (4421450493335847/100000000000000 : ℝ)*(major0) + (4421450493335847/100000000000000 : ℝ)*(major1) + (4421450493335847/100000000000000 : ℝ)*(major2) + (5997644269822423/100000000000000 : ℝ)*(sp0) + (5997672560471243/100000000000000 : ℝ)*(sp1) + (749709066586459/12500000000000 : ℝ)*(sp2) + (1422605994395427/50000000000000 : ℝ)*(sp3) + (29542785819/100000000000000 : ℝ)*(sp4) + (14938107551/100000000000000 : ℝ)*(sp7) + (569045385379681/20000000000000 : ℝ)*(f.failure) + (2998836906304121/50000000000000 : ℝ)*(f.sum) + (22836796310777/5905000000000000000000000000 : ℝ)*base66 + (6915316342337940153/1181000000000000000000000000000000 : ℝ)*base67 + (15380887979335940153/1181000000000000000000000000000000 : ℝ)*base69 + (4630422699758940153/1181000000000000000000000000000000 : ℝ)*base71 + (310808527703/369062500000000000000000000 : ℝ)*base73 + (6194104208225059847/1181000000000000000000000000000000 : ℝ)*base76 + (3264038329607940153/1181000000000000000000000000000000 : ℝ)*base77 + (3976443066277059847/1181000000000000000000000000000000 : ℝ)*base80 + (7833400717613/5905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (836047/200000000000000000000 : ℝ)*base89 + (836047/200000000000000000000 : ℝ)*base91 + (836047/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1772610769444949104760337849/295250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1038830397/100000000000000 : ℝ)*(base19) + (1128590077/100000000000000 : ℝ)*(base23) + (122219279/100000000000000 : ℝ)*(upper3) + (40725287/100000000000000 : ℝ)*(lower4) + (123222841/100000000000000 : ℝ)*(upper5) + (4453424303106717/100000000000000 : ℝ)*(major0) + (4453424303106717/100000000000000 : ℝ)*(major1) + (4453424303106717/100000000000000 : ℝ)*(major2) + (21336955177/100000000000000 : ℝ)*(sp1) + (11470032297/50000000000000 : ℝ)*(sp2) + (6041046162412301/100000000000000 : ℝ)*(sp4) + (6041023786626727/100000000000000 : ℝ)*(sp5) + (604102209375763/10000000000000 : ℝ)*(sp6) + (1432901121837861/50000000000000 : ℝ)*(sp7) + (1432901121837861/50000000000000 : ℝ)*(f.failure) + (6041046162412301/100000000000000 : ℝ)*(f.sum) + (6554321766133/1476250000000000000000000000 : ℝ)*base66 + (13894005998863870717/1181000000000000000000000000000000 : ℝ)*base68 + (4523918079706129283/1181000000000000000000000000000000 : ℝ)*base69 + (13076256626618870717/1181000000000000000000000000000000 : ℝ)*base72 + (28268555412297/5905000000000000000000000000 : ℝ)*base74 + (218035301600870717/1181000000000000000000000000000000 : ℝ)*base76 + (8038227082666870717/1181000000000000000000000000000000 : ℝ)*base78 + (8074956343282870717/1181000000000000000000000000000000 : ℝ)*base80 + (5271703328869/2952500000000000000000000000 : ℝ)*base81 + (7261707/500000000000000000000 : ℝ)*base89 + (7261707/500000000000000000000 : ℝ)*base91 + (7261707/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1359_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2797/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1359_s7_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014688949/5000000000 : ℝ)*x 0 + (5411787311/10000000000 : ℝ)*x 1 + (5245156363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014688949/5000000000 : ℝ)^4319 ≤ (6181294078301/50000000000000 : ℝ)^3295 := by
    have hnat : (1014688949 : ℕ)^4319*50000000000000^3295 ≤ 6181294078301^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014688949 5000000000 6181294078301 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411787311/10000000000 : ℝ)^4319 ≤ (22358361821879/50000000000000 : ℝ)^3295 := by
    have hnat : (5411787311 : ℕ)^4319*50000000000000^3295 ≤ 22358361821879^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411787311 10000000000 22358361821879 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245156363/10000000000 : ℝ)^4319 ≤ (42920688184921/100000000000000 : ℝ)^3295 := by
    have hnat : (5245156363 : ℕ)^4319*100000000000000^3295 ≤ 42920688184921^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245156363 10000000000 42920688184921 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014688949/5000000000 : ℝ), (5411787311/10000000000 : ℝ), (5245156363/10000000000 : ℝ)] ![(6181294078301/50000000000000 : ℝ), (22358361821879/50000000000000 : ℝ), (42920688184921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014688949/5000000000 : ℝ)|^4319 ≤ (6181294078301/50000000000000 : ℝ)^3295
        have hw : |(-1014688949/5000000000 : ℝ)|=(1014688949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411787311/10000000000 : ℝ)|^4319 ≤ (22358361821879/50000000000000 : ℝ)^3295
        have hw : |(5411787311/10000000000 : ℝ)|=(5411787311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245156363/10000000000 : ℝ)|^4319 ≤ (42920688184921/100000000000000 : ℝ)^3295
        have hw : |(5245156363/10000000000 : ℝ)|=(5245156363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337171893/2500000000 : ℝ)*x 0 + (-2114263429/10000000000 : ℝ)*x 1 + (5245156347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337171893/2500000000 : ℝ)^4319 ≤ (44034550010747/100000000000000 : ℝ)^3295 := by
    have hnat : (1337171893 : ℕ)^4319*100000000000000^3295 ≤ 44034550010747^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337171893 2500000000 44034550010747 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114263429/10000000000 : ℝ)^4319 ≤ (3261190491843/25000000000000 : ℝ)^3295 := by
    have hnat : (2114263429 : ℕ)^4319*25000000000000^3295 ≤ 3261190491843^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114263429 10000000000 3261190491843 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245156347/10000000000 : ℝ)^4319 ≤ (8584137602661/20000000000000 : ℝ)^3295 := by
    have hnat : (5245156347 : ℕ)^4319*20000000000000^3295 ≤ 8584137602661^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245156347 10000000000 8584137602661 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337171893/2500000000 : ℝ), (-2114263429/10000000000 : ℝ), (5245156347/10000000000 : ℝ)] ![(44034550010747/100000000000000 : ℝ), (3261190491843/25000000000000 : ℝ), (8584137602661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337171893/2500000000 : ℝ)|^4319 ≤ (44034550010747/100000000000000 : ℝ)^3295
        have hw : |(1337171893/2500000000 : ℝ)|=(1337171893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114263429/10000000000 : ℝ)|^4319 ≤ (3261190491843/25000000000000 : ℝ)^3295
        have hw : |(-2114263429/10000000000 : ℝ)|=(2114263429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245156347/10000000000 : ℝ)|^4319 ≤ (8584137602661/20000000000000 : ℝ)^3295
        have hw : |(5245156347/10000000000 : ℝ)|=(5245156347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267434377/500000000 : ℝ)*x 0 + (5245156381/10000000000 : ℝ)*x 1 + (-84570537/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267434377/500000000 : ℝ)^4319 ≤ (1761381986617/4000000000000 : ℝ)^3295 := by
    have hnat : (267434377 : ℕ)^4319*4000000000000^3295 ≤ 1761381986617^3295*500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267434377 500000000 1761381986617 4000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245156381/10000000000 : ℝ)^4319 ≤ (10730172094497/25000000000000 : ℝ)^3295 := by
    have hnat : (5245156381 : ℕ)^4319*25000000000000^3295 ≤ 10730172094497^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245156381 10000000000 10730172094497 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84570537/400000000 : ℝ)^4319 ≤ (13044761935023/100000000000000 : ℝ)^3295 := by
    have hnat : (84570537 : ℕ)^4319*100000000000000^3295 ≤ 13044761935023^3295*400000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84570537 400000000 13044761935023 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267434377/500000000 : ℝ), (5245156381/10000000000 : ℝ), (-84570537/400000000 : ℝ)] ![(1761381986617/4000000000000 : ℝ), (10730172094497/25000000000000 : ℝ), (13044761935023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267434377/500000000 : ℝ)|^4319 ≤ (1761381986617/4000000000000 : ℝ)^3295
        have hw : |(267434377/500000000 : ℝ)|=(267434377/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245156381/10000000000 : ℝ)|^4319 ≤ (10730172094497/25000000000000 : ℝ)^3295
        have hw : |(5245156381/10000000000 : ℝ)|=(5245156381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84570537/400000000 : ℝ)|^4319 ≤ (13044761935023/100000000000000 : ℝ)^3295
        have hw : |(-84570537/400000000 : ℝ)|=(84570537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270137263/625000000 : ℝ)*x 0 + (4149878923/10000000000 : ℝ)*x 1 + (2250566549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270137263/625000000 : ℝ)^4319 ≤ (33303581303309/100000000000000 : ℝ)^3295 := by
    have hnat : (270137263 : ℕ)^4319*100000000000000^3295 ≤ 33303581303309^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270137263 625000000 33303581303309 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149878923/10000000000 : ℝ)^4319 ≤ (31574087313621/100000000000000 : ℝ)^3295 := by
    have hnat : (4149878923 : ℕ)^4319*100000000000000^3295 ≤ 31574087313621^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149878923 10000000000 31574087313621 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250566549/5000000000 : ℝ)^4319 ≤ (7024466275127/20000000000000 : ℝ)^3295 := by
    have hnat : (2250566549 : ℕ)^4319*20000000000000^3295 ≤ 7024466275127^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250566549 5000000000 7024466275127 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270137263/625000000 : ℝ), (4149878923/10000000000 : ℝ), (2250566549/5000000000 : ℝ)] ![(33303581303309/100000000000000 : ℝ), (31574087313621/100000000000000 : ℝ), (7024466275127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270137263/625000000 : ℝ)|^4319 ≤ (33303581303309/100000000000000 : ℝ)^3295
        have hw : |(270137263/625000000 : ℝ)|=(270137263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149878923/10000000000 : ℝ)|^4319 ≤ (31574087313621/100000000000000 : ℝ)^3295
        have hw : |(4149878923/10000000000 : ℝ)|=(4149878923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250566549/5000000000 : ℝ)|^4319 ≤ (7024466275127/20000000000000 : ℝ)^3295
        have hw : |(2250566549/5000000000 : ℝ)|=(2250566549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50734751/250000000 : ℝ)*x 0 + (65571917/125000000 : ℝ)*x 1 + (1352796779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50734751/250000000 : ℝ)^4319 ≤ (2472537022083/20000000000000 : ℝ)^3295 := by
    have hnat : (50734751 : ℕ)^4319*20000000000000^3295 ≤ 2472537022083^3295*250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50734751 250000000 2472537022083 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65571917/125000000 : ℝ)^4319 ≤ (42927091661889/100000000000000 : ℝ)^3295 := by
    have hnat : (65571917 : ℕ)^4319*100000000000000^3295 ≤ 42927091661889^3295*125000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65571917 125000000 42927091661889 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352796779/2500000000 : ℝ)^4319 ≤ (44710223216101/100000000000000 : ℝ)^3295 := by
    have hnat : (1352796779 : ℕ)^4319*100000000000000^3295 ≤ 44710223216101^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352796779 2500000000 44710223216101 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50734751/250000000 : ℝ), (65571917/125000000 : ℝ), (1352796779/2500000000 : ℝ)] ![(2472537022083/20000000000000 : ℝ), (42927091661889/100000000000000 : ℝ), (44710223216101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50734751/250000000 : ℝ)|^4319 ≤ (2472537022083/20000000000000 : ℝ)^3295
        have hw : |(-50734751/250000000 : ℝ)|=(50734751/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65571917/125000000 : ℝ)|^4319 ≤ (42927091661889/100000000000000 : ℝ)^3295
        have hw : |(65571917/125000000 : ℝ)|=(65571917/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352796779/2500000000 : ℝ)|^4319 ≤ (44710223216101/100000000000000 : ℝ)^3295
        have hw : |(1352796779/2500000000 : ℝ)|=(1352796779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305684467/10000000000 : ℝ)*x 0 + (-121764547/625000000 : ℝ)*x 1 + (2705593427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305684467/10000000000 : ℝ)^4319 ≤ (21785535526807/50000000000000 : ℝ)^3295 := by
    have hnat : (5305684467 : ℕ)^4319*50000000000000^3295 ≤ 21785535526807^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305684467 10000000000 21785535526807 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121764547/625000000 : ℝ)^4319 ≤ (11718708559369/100000000000000 : ℝ)^3295 := by
    have hnat : (121764547 : ℕ)^4319*100000000000000^3295 ≤ 11718708559369^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121764547 625000000 11718708559369 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705593427/5000000000 : ℝ)^4319 ≤ (5588777547319/12500000000000 : ℝ)^3295 := by
    have hnat : (2705593427 : ℕ)^4319*12500000000000^3295 ≤ 5588777547319^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705593427 5000000000 5588777547319 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305684467/10000000000 : ℝ), (-121764547/625000000 : ℝ), (2705593427/5000000000 : ℝ)] ![(21785535526807/50000000000000 : ℝ), (11718708559369/100000000000000 : ℝ), (5588777547319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305684467/10000000000 : ℝ)|^4319 ≤ (21785535526807/50000000000000 : ℝ)^3295
        have hw : |(5305684467/10000000000 : ℝ)|=(5305684467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121764547/625000000 : ℝ)|^4319 ≤ (11718708559369/100000000000000 : ℝ)^3295
        have hw : |(-121764547/625000000 : ℝ)|=(121764547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705593427/5000000000 : ℝ)|^4319 ≤ (5588777547319/12500000000000 : ℝ)^3295
        have hw : |(2705593427/5000000000 : ℝ)|=(2705593427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326421103/2500000000 : ℝ)*x 0 + (1352796743/2500000000 : ℝ)*x 1 + (-389646533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326421103/2500000000 : ℝ)^4319 ≤ (2178553523079/5000000000000 : ℝ)^3295 := by
    have hnat : (1326421103 : ℕ)^4319*5000000000000^3295 ≤ 2178553523079^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326421103 2500000000 2178553523079 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352796743/2500000000 : ℝ)^4319 ≤ (44710221656533/100000000000000 : ℝ)^3295 := by
    have hnat : (1352796743 : ℕ)^4319*100000000000000^3295 ≤ 44710221656533^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352796743 2500000000 44710221656533 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389646533/2000000000 : ℝ)^4319 ≤ (1171870787343/10000000000000 : ℝ)^3295 := by
    have hnat : (389646533 : ℕ)^4319*10000000000000^3295 ≤ 1171870787343^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389646533 2000000000 1171870787343 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326421103/2500000000 : ℝ), (1352796743/2500000000 : ℝ), (-389646533/2000000000 : ℝ)] ![(2178553523079/5000000000000 : ℝ), (44710221656533/100000000000000 : ℝ), (1171870787343/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326421103/2500000000 : ℝ)|^4319 ≤ (2178553523079/5000000000000 : ℝ)^3295
        have hw : |(1326421103/2500000000 : ℝ)|=(1326421103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352796743/2500000000 : ℝ)|^4319 ≤ (44710221656533/100000000000000 : ℝ)^3295
        have hw : |(1352796743/2500000000 : ℝ)|=(1352796743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389646533/2000000000 : ℝ)|^4319 ≤ (1171870787343/10000000000000 : ℝ)^3295
        have hw : |(-389646533/2000000000 : ℝ)|=(389646533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s7_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (864444341/2000000000 : ℝ)*x 0 + (2249937213/5000000000 : ℝ)*x 1 + (4151143843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864444341/2000000000 : ℝ)^4319 ≤ (16651919409509/50000000000000 : ℝ)^3295 := by
    have hnat : (864444341 : ℕ)^4319*50000000000000^3295 ≤ 16651919409509^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864444341 2000000000 16651919409509 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249937213/5000000000 : ℝ)^4319 ≤ (7021891656183/20000000000000 : ℝ)^3295 := by
    have hnat : (2249937213 : ℕ)^4319*20000000000000^3295 ≤ 7021891656183^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249937213 5000000000 7021891656183 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4151143843/10000000000 : ℝ)^4319 ≤ (31586702881129/100000000000000 : ℝ)^3295 := by
    have hnat : (4151143843 : ℕ)^4319*100000000000000^3295 ≤ 31586702881129^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151143843 10000000000 31586702881129 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864444341/2000000000 : ℝ), (2249937213/5000000000 : ℝ), (4151143843/10000000000 : ℝ)] ![(16651919409509/50000000000000 : ℝ), (7021891656183/20000000000000 : ℝ), (31586702881129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864444341/2000000000 : ℝ)|^4319 ≤ (16651919409509/50000000000000 : ℝ)^3295
        have hw : |(864444341/2000000000 : ℝ)|=(864444341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249937213/5000000000 : ℝ)|^4319 ≤ (7021891656183/20000000000000 : ℝ)^3295
        have hw : |(2249937213/5000000000 : ℝ)|=(2249937213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4151143843/10000000000 : ℝ)|^4319 ≤ (31586702881129/100000000000000 : ℝ)^3295
        have hw : |(4151143843/10000000000 : ℝ)|=(4151143843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2797/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11189/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2797/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2797/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2797/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2797/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2797/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2797/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2797/25000 : ℝ) ^ (2159/512 : ℝ) ≤ (2436252764572573/25000000000000000000 : ℝ) := by
    have hpowers : (2797/25000 : ℝ)^2159 ≤ (2436252764572573/25000000000000000000 : ℝ)^512 := by
      have hnat : (2797 : ℕ)^2159*25000000000000000000^512 ≤ 2436252764572573^512*25000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2797 25000 2436252764572573 25000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2797/25000 : ℝ)) (X := (2436252764572573/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7359/50000 : ℝ) ^ (2159/512 : ℝ) ≤ (30973295388822709/100000000000000000000 : ℝ) := by
    have hpowers : (7359/50000 : ℝ)^2159 ≤ (30973295388822709/100000000000000000000 : ℝ)^512 := by
      have hnat : (7359 : ℕ)^2159*100000000000000000000^512 ≤ 30973295388822709^512*50000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7359 50000 30973295388822709 100000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7359/50000 : ℝ)) (X := (30973295388822709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502436252764572573/12500000000000000000 : ℝ) ≤ (31251444266671/31250000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (12502436252764572573/12500000000000000000 : ℝ)^512 ≤ (31251444266671/31250000000000 : ℝ)^2159 := by
      have hnat : (12502436252764572573 : ℕ)^512*31250000000000^2159 ≤ 31251444266671^2159*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502436252764572573 12500000000000000000 31251444266671 31250000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31251444266671/31250000000000 : ℝ)) (X := (12502436252764572573/12500000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040718306447113001/100000000000000000000 : ℝ) ≤ (2500241367945791/2500000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (100040718306447113001/100000000000000000000 : ℝ)^512 ≤ (2500241367945791/2500000000000000 : ℝ)^2159 := by
      have hnat : (100040718306447113001 : ℕ)^512*2500000000000000^2159 ≤ 2500241367945791^2159*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040718306447113001 100000000000000000000 2500241367945791 2500000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500241367945791/2500000000000000 : ℝ)) (X := (100040718306447113001/100000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030973295388822709/50000000000000000000 : ℝ) ≤ (1250183597278951/1250000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (50030973295388822709/50000000000000000000 : ℝ)^512 ≤ (1250183597278951/1250000000000000 : ℝ)^2159 := by
      have hnat : (50030973295388822709 : ℕ)^512*1250000000000000^2159 ≤ 1250183597278951^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030973295388822709 50000000000000000000 1250183597278951 1250000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250183597278951/1250000000000000 : ℝ)) (X := (50030973295388822709/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2436252764572573/25000000000000000000 : ℝ) ≤ ((1102824045579411833/1103125000000000000 : ℝ)+2*(125826612111/88250000000000 : ℝ)*(2797/25000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (1102824045579411833/1103125000000000000 : ℝ)+2*(125826612111/88250000000000 : ℝ)*(2797/25000 : ℝ)=(31251444266671/31250000000000 : ℝ) by norm_num, show 1+2*(2436252764572573/25000000000000000000 : ℝ)=(12502436252764572573/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30973295388822709/100000000000000000000 : ℝ)+(2436252764572573/25000000000000000000 : ℝ) ≤ ((1102824045579411833/1103125000000000000 : ℝ)+(125826612111/88250000000000 : ℝ)*((7359/50000 : ℝ)+(2797/25000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (1102824045579411833/1103125000000000000 : ℝ)+(125826612111/88250000000000 : ℝ)*((7359/50000 : ℝ)+(2797/25000 : ℝ))=(2500241367945791/2500000000000000 : ℝ) by norm_num, show 1+(30973295388822709/100000000000000000000 : ℝ)+(2436252764572573/25000000000000000000 : ℝ)=(100040718306447113001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30973295388822709/100000000000000000000 : ℝ) ≤ ((1102824045579411833/1103125000000000000 : ℝ)+2*(125826612111/88250000000000 : ℝ)*(7359/50000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (1102824045579411833/1103125000000000000 : ℝ)+2*(125826612111/88250000000000 : ℝ)*(7359/50000 : ℝ)=(1250183597278951/1250000000000000 : ℝ) by norm_num, show 1+2*(30973295388822709/100000000000000000000 : ℝ)=(50030973295388822709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1102824045579411833/1103125000000000000 : ℝ)*(X 1 0+X 2 0)+(125826612111/88250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (2797/25000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (1102824045579411833/1103125000000000000 : ℝ)) (alpha := (125826612111/88250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1102824045579411833/1103125000000000000 : ℝ)*(X 0 1+X 2 1)+(125826612111/88250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (2797/25000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (1102824045579411833/1103125000000000000 : ℝ)) (alpha := (125826612111/88250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1102824045579411833/1103125000000000000 : ℝ)*(X 0 2+X 1 2)+(125826612111/88250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (2797/25000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (1102824045579411833/1103125000000000000 : ℝ)) (alpha := (125826612111/88250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1014688949/5000000000 : ℝ)*X 0 0+(5411787311/10000000000 : ℝ)*X 0 1+(5245156363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337171893/2500000000 : ℝ)*X 1 0+(-2114263429/10000000000 : ℝ)*X 1 1+(5245156347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267434377/500000000 : ℝ)*X 2 0+(5245156381/10000000000 : ℝ)*X 2 1+(-84570537/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270137263/625000000 : ℝ)*X 0 0+(4149878923/10000000000 : ℝ)*X 0 1+(2250566549/5000000000 : ℝ)*X 0 2+(270137263/625000000 : ℝ)*X 1 0+(4149878923/10000000000 : ℝ)*X 1 1+(2250566549/5000000000 : ℝ)*X 1 2+(270137263/625000000 : ℝ)*X 2 0+(4149878923/10000000000 : ℝ)*X 2 1+(2250566549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50734751/250000000 : ℝ)*X 0 0+(65571917/125000000 : ℝ)*X 0 1+(1352796779/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305684467/10000000000 : ℝ)*X 1 0+(-121764547/625000000 : ℝ)*X 1 1+(2705593427/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326421103/2500000000 : ℝ)*X 2 0+(1352796743/2500000000 : ℝ)*X 2 1+(-389646533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864444341/2000000000 : ℝ)*X 0 0+(2249937213/5000000000 : ℝ)*X 0 1+(4151143843/10000000000 : ℝ)*X 0 2+(864444341/2000000000 : ℝ)*X 1 0+(2249937213/5000000000 : ℝ)*X 1 1+(4151143843/10000000000 : ℝ)*X 1 2+(864444341/2000000000 : ℝ)*X 2 0+(2249937213/5000000000 : ℝ)*X 2 1+(4151143843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (211845137220076799258085651/27578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (712243337/50000000000000 : ℝ)*(base19) + (257756689/20000000000000 : ℝ)*(base23) + (53379107/100000000000000 : ℝ)*(lower2) + (167419859/100000000000000 : ℝ)*(upper3) + (91860151/100000000000000 : ℝ)*(upper5) + (2212079575622599/50000000000000 : ℝ)*(major0) + (2212079575622599/50000000000000 : ℝ)*(major1) + (2212079575622599/50000000000000 : ℝ)*(major2) + (3000658975417993/50000000000000 : ℝ)*(sp0) + (6001346659268481/100000000000000 : ℝ)*(sp1) + (600134679497171/10000000000000 : ℝ)*(sp2) + (1423477425332047/50000000000000 : ℝ)*(sp3) + (30132919169/100000000000000 : ℝ)*(sp4) + (7556008293/50000000000000 : ℝ)*(sp7) + (71174249067017/2500000000000 : ℝ)*(f.failure) + (1200269616751031/20000000000000 : ℝ)*(f.sum) + (24558628786797/4412500000000000000000000000 : ℝ)*base66 + (25245054182051467/55156250000000000000000000000000 : ℝ)*base67 + (148707656340448533/55156250000000000000000000000000 : ℝ)*base70 + (77173509136738967/55156250000000000000000000000000 : ℝ)*base71 + (1984800178531/8825000000000000000000000000 : ℝ)*base73 + (236664963356854783/55156250000000000000000000000000 : ℝ)*base76 + (308560361113886033/55156250000000000000000000000000 : ℝ)*base78 + (810584486204198533/55156250000000000000000000000000 : ℝ)*base80 + (3178887309193/1103125000000000000000000000 : ℝ)*base82 + (107079/25000000000000000000 : ℝ)*base89 + (107079/25000000000000000000 : ℝ)*base91 + (107079/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77414312972563381246223139/13789062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1754276887/100000000000000 : ℝ)*(base19) + (869410401/50000000000000 : ℝ)*(base23) + (47823043/10000000000000 : ℝ)*(lower1) + (42100917/25000000000000 : ℝ)*(upper3) + (705167/6250000000000 : ℝ)*(lower4) + (175765263/100000000000000 : ℝ)*(upper5) + (1114026969823611/25000000000000 : ℝ)*(major0) + (1114026969823611/25000000000000 : ℝ)*(major1) + (1114026969823611/25000000000000 : ℝ)*(major2) + (800092383/25000000000000 : ℝ)*(sp2) + (6044686432212829/100000000000000 : ℝ)*(sp4) + (6044684677935943/100000000000000 : ℝ)*(sp5) + (1208936298604499/20000000000000 : ℝ)*(sp6) + (2867529139236627/100000000000000 : ℝ)*(sp7) + (2867529139236627/100000000000000 : ℝ)*(f.failure) + (6044686432212829/100000000000000 : ℝ)*(f.sum) + (32022071975693/8825000000000000000000000000 : ℝ)*base65 + (941061261724107713/27578125000000000000000000000000 : ℝ)*base67 + (60304042598844581/13789062500000000000000000000000 : ℝ)*base70 + (1784090625355201463/27578125000000000000000000000000 : ℝ)*base71 + (20107468211309/4412500000000000000000000000 : ℝ)*base73 + (5458380244326429/215454101562500000000000000000 : ℝ)*base76 + (17943320012117603/6894531250000000000000000000000 : ℝ)*base78 + (57621611508392287/27578125000000000000000000000000 : ℝ)*base80 + (8446592888191/4412500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9841149/1000000000000000000000 : ℝ)*base89 + (9841149/1000000000000000000000 : ℝ)*base91 + (9841149/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1359_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2797/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1359_box_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-931730059/5000000000 : ℝ)*x 0 + (673653503/1250000000 : ℝ)*x 1 + (2694614329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931730059/5000000000 : ℝ)^4319 ≤ (21591592441/195312500000 : ℝ)^3295 := by
    have hnat : (931730059 : ℕ)^4319*195312500000^3295 ≤ 21591592441^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931730059 5000000000 21591592441 195312500000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673653503/1250000000 : ℝ)^4319 ≤ (44472548900349/100000000000000 : ℝ)^3295 := by
    have hnat : (673653503 : ℕ)^4319*100000000000000^3295 ≤ 44472548900349^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673653503 1250000000 44472548900349 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694614329/5000000000 : ℝ)^4319 ≤ (44472555758113/100000000000000 : ℝ)^3295 := by
    have hnat : (2694614329 : ℕ)^4319*100000000000000^3295 ≤ 44472555758113^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694614329 5000000000 44472555758113 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931730059/5000000000 : ℝ), (673653503/1250000000 : ℝ), (2694614329/5000000000 : ℝ)] ![(21591592441/195312500000 : ℝ), (44472548900349/100000000000000 : ℝ), (44472555758113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931730059/5000000000 : ℝ)|^4319 ≤ (21591592441/195312500000 : ℝ)^3295
        have hw : |(-931730059/5000000000 : ℝ)|=(931730059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673653503/1250000000 : ℝ)|^4319 ≤ (44472548900349/100000000000000 : ℝ)^3295
        have hw : |(673653503/1250000000 : ℝ)|=(673653503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694614329/5000000000 : ℝ)|^4319 ≤ (44472555758113/100000000000000 : ℝ)^3295
        have hw : |(2694614329/5000000000 : ℝ)|=(2694614329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642693319/5000000000 : ℝ)*x 0 + (-2005810347/10000000000 : ℝ)*x 1 + (5389227959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642693319/5000000000 : ℝ)^4319 ≤ (2167635486533/5000000000000 : ℝ)^3295 := by
    have hnat : (2642693319 : ℕ)^4319*5000000000000^3295 ≤ 2167635486533^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642693319 5000000000 2167635486533 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005810347/10000000000 : ℝ)^4319 ≤ (12174742048273/100000000000000 : ℝ)^3295 := by
    have hnat : (2005810347 : ℕ)^4319*100000000000000^3295 ≤ 12174742048273^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005810347 10000000000 12174742048273 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389227959/10000000000 : ℝ)^4319 ≤ (22236274098633/50000000000000 : ℝ)^3295 := by
    have hnat : (5389227959 : ℕ)^4319*50000000000000^3295 ≤ 22236274098633^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389227959 10000000000 22236274098633 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642693319/5000000000 : ℝ), (-2005810347/10000000000 : ℝ), (5389227959/10000000000 : ℝ)] ![(2167635486533/5000000000000 : ℝ), (12174742048273/100000000000000 : ℝ), (22236274098633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642693319/5000000000 : ℝ)|^4319 ≤ (2167635486533/5000000000000 : ℝ)^3295
        have hw : |(2642693319/5000000000 : ℝ)|=(2642693319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005810347/10000000000 : ℝ)|^4319 ≤ (12174742048273/100000000000000 : ℝ)^3295
        have hw : |(-2005810347/10000000000 : ℝ)|=(2005810347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389227959/10000000000 : ℝ)|^4319 ≤ (22236274098633/50000000000000 : ℝ)^3295
        have hw : |(5389227959/10000000000 : ℝ)|=(5389227959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285386441/10000000000 : ℝ)*x 0 + (2694614071/5000000000 : ℝ)*x 1 + (-401162073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285386441/10000000000 : ℝ)^4319 ≤ (2709544225789/6250000000000 : ℝ)^3295 := by
    have hnat : (5285386441 : ℕ)^4319*6250000000000^3295 ≤ 2709544225789^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285386441 10000000000 2709544225789 6250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694614071/5000000000 : ℝ)^4319 ≤ (8894510035343/20000000000000 : ℝ)^3295 := by
    have hnat : (2694614071 : ℕ)^4319*20000000000000^3295 ≤ 8894510035343^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694614071 5000000000 8894510035343 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401162073/2000000000 : ℝ)^4319 ≤ (6087371095741/50000000000000 : ℝ)^3295 := by
    have hnat : (401162073 : ℕ)^4319*50000000000000^3295 ≤ 6087371095741^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401162073 2000000000 6087371095741 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285386441/10000000000 : ℝ), (2694614071/5000000000 : ℝ), (-401162073/2000000000 : ℝ)] ![(2709544225789/6250000000000 : ℝ), (8894510035343/20000000000000 : ℝ), (6087371095741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285386441/10000000000 : ℝ)|^4319 ≤ (2709544225789/6250000000000 : ℝ)^3295
        have hw : |(5285386441/10000000000 : ℝ)|=(5285386441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694614071/5000000000 : ℝ)|^4319 ≤ (8894510035343/20000000000000 : ℝ)^3295
        have hw : |(2694614071/5000000000 : ℝ)|=(2694614071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-401162073/2000000000 : ℝ)|^4319 ≤ (6087371095741/50000000000000 : ℝ)^3295
        have hw : |(-401162073/2000000000 : ℝ)|=(401162073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4469993199/10000000000 : ℝ)*x 0 + (2126074801/5000000000 : ℝ)*x 1 + (2126074933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4469993199/10000000000 : ℝ)^4319 ≤ (6960835297307/20000000000000 : ℝ)^3295 := by
    have hnat : (4469993199 : ℕ)^4319*20000000000000^3295 ≤ 6960835297307^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469993199 10000000000 6960835297307 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126074801/5000000000 : ℝ)^4319 ≤ (32597910426387/100000000000000 : ℝ)^3295 := by
    have hnat : (2126074801 : ℕ)^4319*100000000000000^3295 ≤ 32597910426387^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126074801 5000000000 32597910426387 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126074933/5000000000 : ℝ)^4319 ≤ (16298956539619/50000000000000 : ℝ)^3295 := by
    have hnat : (2126074933 : ℕ)^4319*50000000000000^3295 ≤ 16298956539619^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126074933 5000000000 16298956539619 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4469993199/10000000000 : ℝ), (2126074801/5000000000 : ℝ), (2126074933/5000000000 : ℝ)] ![(6960835297307/20000000000000 : ℝ), (32597910426387/100000000000000 : ℝ), (16298956539619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4469993199/10000000000 : ℝ)|^4319 ≤ (6960835297307/20000000000000 : ℝ)^3295
        have hw : |(4469993199/10000000000 : ℝ)|=(4469993199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126074801/5000000000 : ℝ)|^4319 ≤ (32597910426387/100000000000000 : ℝ)^3295
        have hw : |(2126074801/5000000000 : ℝ)|=(2126074801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126074933/5000000000 : ℝ)|^4319 ≤ (16298956539619/50000000000000 : ℝ)^3295
        have hw : |(2126074933/5000000000 : ℝ)|=(2126074933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219804409/1000000000 : ℝ)*x 0 + (5265289843/10000000000 : ℝ)*x 1 + (5265290457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219804409/1000000000 : ℝ)^4319 ≤ (13726457998511/100000000000000 : ℝ)^3295 := by
    have hnat : (219804409 : ℕ)^4319*100000000000000^3295 ≤ 13726457998511^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219804409 1000000000 13726457998511 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265289843/10000000000 : ℝ)^4319 ≤ (269604798137/625000000000 : ℝ)^3295 := by
    have hnat : (5265289843 : ℕ)^4319*625000000000^3295 ≤ 269604798137^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265289843 10000000000 269604798137 625000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265290457/10000000000 : ℝ)^4319 ≤ (43136774295503/100000000000000 : ℝ)^3295 := by
    have hnat : (5265290457 : ℕ)^4319*100000000000000^3295 ≤ 43136774295503^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265290457 10000000000 43136774295503 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219804409/1000000000 : ℝ), (5265289843/10000000000 : ℝ), (5265290457/10000000000 : ℝ)] ![(13726457998511/100000000000000 : ℝ), (269604798137/625000000000 : ℝ), (43136774295503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219804409/1000000000 : ℝ)|^4319 ≤ (13726457998511/100000000000000 : ℝ)^3295
        have hw : |(-219804409/1000000000 : ℝ)|=(219804409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265289843/10000000000 : ℝ)|^4319 ≤ (269604798137/625000000000 : ℝ)^3295
        have hw : |(5265289843/10000000000 : ℝ)|=(5265289843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265290457/10000000000 : ℝ)|^4319 ≤ (43136774295503/100000000000000 : ℝ)^3295
        have hw : |(5265290457/10000000000 : ℝ)|=(5265290457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372375331/10000000000 : ℝ)*x 0 + (-128478791/625000000 : ℝ)*x 1 + (210611623/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372375331/10000000000 : ℝ)^4319 ≤ (44290347661931/100000000000000 : ℝ)^3295 := by
    have hnat : (5372375331 : ℕ)^4319*100000000000000^3295 ≤ 44290347661931^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372375331 10000000000 44290347661931 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128478791/625000000 : ℝ)^4319 ≤ (6286438377929/50000000000000 : ℝ)^3295 := by
    have hnat : (128478791 : ℕ)^4319*50000000000000^3295 ≤ 6286438377929^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128478791 625000000 6286438377929 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210611623/400000000 : ℝ)^4319 ≤ (43136775562673/100000000000000 : ℝ)^3295 := by
    have hnat : (210611623 : ℕ)^4319*100000000000000^3295 ≤ 43136775562673^3295*400000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210611623 400000000 43136775562673 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372375331/10000000000 : ℝ), (-128478791/625000000 : ℝ), (210611623/400000000 : ℝ)] ![(44290347661931/100000000000000 : ℝ), (6286438377929/50000000000000 : ℝ), (43136775562673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372375331/10000000000 : ℝ)|^4319 ≤ (44290347661931/100000000000000 : ℝ)^3295
        have hw : |(5372375331/10000000000 : ℝ)|=(5372375331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128478791/625000000 : ℝ)|^4319 ≤ (6286438377929/50000000000000 : ℝ)^3295
        have hw : |(-128478791/625000000 : ℝ)|=(128478791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210611623/400000000 : ℝ)|^4319 ≤ (43136775562673/100000000000000 : ℝ)^3295
        have hw : |(210611623/400000000 : ℝ)|=(210611623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686187509/5000000000 : ℝ)*x 0 + (2632645417/5000000000 : ℝ)*x 1 + (-2055660731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686187509/5000000000 : ℝ)^4319 ≤ (44290344279609/100000000000000 : ℝ)^3295 := by
    have hnat : (2686187509 : ℕ)^4319*100000000000000^3295 ≤ 44290344279609^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686187509 5000000000 44290344279609 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632645417/5000000000 : ℝ)^4319 ≤ (21568389172003/50000000000000 : ℝ)^3295 := by
    have hnat : (2632645417 : ℕ)^4319*50000000000000^3295 ≤ 21568389172003^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632645417 5000000000 21568389172003 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055660731/10000000000 : ℝ)^4319 ≤ (3143219339283/25000000000000 : ℝ)^3295 := by
    have hnat : (2055660731 : ℕ)^4319*25000000000000^3295 ≤ 3143219339283^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055660731 10000000000 3143219339283 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686187509/5000000000 : ℝ), (2632645417/5000000000 : ℝ), (-2055660731/10000000000 : ℝ)] ![(44290344279609/100000000000000 : ℝ), (21568389172003/50000000000000 : ℝ), (3143219339283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686187509/5000000000 : ℝ)|^4319 ≤ (44290344279609/100000000000000 : ℝ)^3295
        have hw : |(2686187509/5000000000 : ℝ)|=(2686187509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632645417/5000000000 : ℝ)|^4319 ≤ (21568389172003/50000000000000 : ℝ)^3295
        have hw : |(2632645417/5000000000 : ℝ)|=(2632645417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055660731/10000000000 : ℝ)|^4319 ≤ (3143219339283/25000000000000 : ℝ)^3295
        have hw : |(-2055660731/10000000000 : ℝ)|=(2055660731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173449329/10000000000 : ℝ)*x 0 + (4400368497/10000000000 : ℝ)*x 1 + (275023049/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173449329/10000000000 : ℝ)^4319 ≤ (1590468036347/5000000000000 : ℝ)^3295 := by
    have hnat : (4173449329 : ℕ)^4319*5000000000000^3295 ≤ 1590468036347^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173449329 10000000000 1590468036347 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4400368497/10000000000 : ℝ)^4319 ≤ (34095318172723/100000000000000 : ℝ)^3295 := by
    have hnat : (4400368497 : ℕ)^4319*100000000000000^3295 ≤ 34095318172723^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400368497 10000000000 34095318172723 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275023049/625000000 : ℝ)^4319 ≤ (34095321087567/100000000000000 : ℝ)^3295 := by
    have hnat : (275023049 : ℕ)^4319*100000000000000^3295 ≤ 34095321087567^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275023049 625000000 34095321087567 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173449329/10000000000 : ℝ), (4400368497/10000000000 : ℝ), (275023049/625000000 : ℝ)] ![(1590468036347/5000000000000 : ℝ), (34095318172723/100000000000000 : ℝ), (34095321087567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173449329/10000000000 : ℝ)|^4319 ≤ (1590468036347/5000000000000 : ℝ)^3295
        have hw : |(4173449329/10000000000 : ℝ)|=(4173449329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4400368497/10000000000 : ℝ)|^4319 ≤ (34095318172723/100000000000000 : ℝ)^3295
        have hw : |(4400368497/10000000000 : ℝ)|=(4400368497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275023049/625000000 : ℝ)|^4319 ≤ (34095321087567/100000000000000 : ℝ)^3295
        have hw : |(275023049/625000000 : ℝ)|=(275023049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_8 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127737361/10000000000 : ℝ)*x 0 + (5179887523/10000000000 : ℝ)*x 1 + (5403241323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127737361/10000000000 : ℝ)^4319 ≤ (13153837771213/100000000000000 : ℝ)^3295 := by
    have hnat : (2127737361 : ℕ)^4319*100000000000000^3295 ≤ 13153837771213^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127737361 10000000000 13153837771213 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179887523/10000000000 : ℝ)^4319 ≤ (42221974993163/100000000000000 : ℝ)^3295 := by
    have hnat : (5179887523 : ℕ)^4319*100000000000000^3295 ≤ 42221974993163^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179887523 10000000000 42221974993163 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403241323/10000000000 : ℝ)^4319 ≤ (22312093611083/50000000000000 : ℝ)^3295 := by
    have hnat : (5403241323 : ℕ)^4319*50000000000000^3295 ≤ 22312093611083^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403241323 10000000000 22312093611083 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127737361/10000000000 : ℝ), (5179887523/10000000000 : ℝ), (5403241323/10000000000 : ℝ)] ![(13153837771213/100000000000000 : ℝ), (42221974993163/100000000000000 : ℝ), (22312093611083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127737361/10000000000 : ℝ)|^4319 ≤ (13153837771213/100000000000000 : ℝ)^3295
        have hw : |(-2127737361/10000000000 : ℝ)|=(2127737361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179887523/10000000000 : ℝ)|^4319 ≤ (42221974993163/100000000000000 : ℝ)^3295
        have hw : |(5179887523/10000000000 : ℝ)|=(5179887523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403241323/10000000000 : ℝ)|^4319 ≤ (22312093611083/50000000000000 : ℝ)^3295
        have hw : |(5403241323/10000000000 : ℝ)|=(5403241323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_9 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637773583/5000000000 : ℝ)*x 0 + (-2000042773/10000000000 : ℝ)*x 1 + (1080647999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637773583/5000000000 : ℝ)^4319 ≤ (21623475849079/50000000000000 : ℝ)^3295 := by
    have hnat : (2637773583 : ℕ)^4319*50000000000000^3295 ≤ 21623475849079^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637773583 5000000000 21623475849079 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000042773/10000000000 : ℝ)^4319 ≤ (6064437719013/50000000000000 : ℝ)^3295 := by
    have hnat : (2000042773 : ℕ)^4319*50000000000000^3295 ≤ 6064437719013^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000042773 10000000000 6064437719013 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080647999/2000000000 : ℝ)^4319 ≤ (22312086423021/50000000000000 : ℝ)^3295 := by
    have hnat : (1080647999 : ℕ)^4319*50000000000000^3295 ≤ 22312086423021^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080647999 2000000000 22312086423021 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637773583/5000000000 : ℝ), (-2000042773/10000000000 : ℝ), (1080647999/2000000000 : ℝ)] ![(21623475849079/50000000000000 : ℝ), (6064437719013/50000000000000 : ℝ), (22312086423021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637773583/5000000000 : ℝ)|^4319 ≤ (21623475849079/50000000000000 : ℝ)^3295
        have hw : |(2637773583/5000000000 : ℝ)|=(2637773583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000042773/10000000000 : ℝ)|^4319 ≤ (6064437719013/50000000000000 : ℝ)^3295
        have hw : |(-2000042773/10000000000 : ℝ)|=(2000042773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080647999/2000000000 : ℝ)|^4319 ≤ (22312086423021/50000000000000 : ℝ)^3295
        have hw : |(1080647999/2000000000 : ℝ)|=(1080647999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_10 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318886587/2500000000 : ℝ)*x 0 + (5403240549/10000000000 : ℝ)*x 1 + (-500010781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318886587/2500000000 : ℝ)^4319 ≤ (43246942908559/100000000000000 : ℝ)^3295 := by
    have hnat : (1318886587 : ℕ)^4319*100000000000000^3295 ≤ 43246942908559^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318886587 2500000000 43246942908559 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403240549/10000000000 : ℝ)^4319 ≤ (4462417884331/10000000000000 : ℝ)^3295 := by
    have hnat : (5403240549 : ℕ)^4319*10000000000000^3295 ≤ 4462417884331^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403240549 10000000000 4462417884331 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500010781/2500000000 : ℝ)^4319 ≤ (12128878228103/100000000000000 : ℝ)^3295 := by
    have hnat : (500010781 : ℕ)^4319*100000000000000^3295 ≤ 12128878228103^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500010781 2500000000 12128878228103 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318886587/2500000000 : ℝ), (5403240549/10000000000 : ℝ), (-500010781/2500000000 : ℝ)] ![(43246942908559/100000000000000 : ℝ), (4462417884331/10000000000000 : ℝ), (12128878228103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318886587/2500000000 : ℝ)|^4319 ≤ (43246942908559/100000000000000 : ℝ)^3295
        have hw : |(1318886587/2500000000 : ℝ)|=(1318886587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403240549/10000000000 : ℝ)|^4319 ≤ (4462417884331/10000000000000 : ℝ)^3295
        have hw : |(5403240549/10000000000 : ℝ)|=(5403240549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500010781/2500000000 : ℝ)|^4319 ≤ (12128878228103/100000000000000 : ℝ)^3295
        have hw : |(-500010781/2500000000 : ℝ)|=(500010781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_11 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4502961133/10000000000 : ℝ)*x 0 + (847075733/2000000000 : ℝ)*x 1 + (4235378097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4502961133/10000000000 : ℝ)^4319 ≤ (17570514817427/50000000000000 : ℝ)^3295 := by
    have hnat : (4502961133 : ℕ)^4319*50000000000000^3295 ≤ 17570514817427^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502961133 10000000000 17570514817427 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847075733/2000000000 : ℝ)^4319 ≤ (2026843001627/6250000000000 : ℝ)^3295 := by
    have hnat : (847075733 : ℕ)^4319*6250000000000^3295 ≤ 2026843001627^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847075733 2000000000 2026843001627 6250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235378097/10000000000 : ℝ)^4319 ≤ (8107370581347/25000000000000 : ℝ)^3295 := by
    have hnat : (4235378097 : ℕ)^4319*25000000000000^3295 ≤ 8107370581347^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235378097 10000000000 8107370581347 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4502961133/10000000000 : ℝ), (847075733/2000000000 : ℝ), (4235378097/10000000000 : ℝ)] ![(17570514817427/50000000000000 : ℝ), (2026843001627/6250000000000 : ℝ), (8107370581347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4502961133/10000000000 : ℝ)|^4319 ≤ (17570514817427/50000000000000 : ℝ)^3295
        have hw : |(4502961133/10000000000 : ℝ)|=(4502961133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847075733/2000000000 : ℝ)|^4319 ≤ (2026843001627/6250000000000 : ℝ)^3295
        have hw : |(847075733/2000000000 : ℝ)|=(847075733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235378097/10000000000 : ℝ)|^4319 ≤ (8107370581347/25000000000000 : ℝ)^3295
        have hw : |(4235378097/10000000000 : ℝ)|=(4235378097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_12 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1934071047/10000000000 : ℝ)*x 0 + (5472462233/10000000000 : ℝ)*x 1 + (5254208117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1934071047/10000000000 : ℝ)^4319 ≤ (5803589420799/50000000000000 : ℝ)^3295 := by
    have hnat : (1934071047 : ℕ)^4319*50000000000000^3295 ≤ 5803589420799^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934071047 10000000000 5803589420799 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472462233/10000000000 : ℝ)^4319 ≤ (5671877277071/12500000000000 : ℝ)^3295 := by
    have hnat : (5472462233 : ℕ)^4319*12500000000000^3295 ≤ 5671877277071^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472462233 10000000000 5671877277071 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254208117/10000000000 : ℝ)^4319 ≤ (21508901463639/50000000000000 : ℝ)^3295 := by
    have hnat : (5254208117 : ℕ)^4319*50000000000000^3295 ≤ 21508901463639^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254208117 10000000000 21508901463639 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1934071047/10000000000 : ℝ), (5472462233/10000000000 : ℝ), (5254208117/10000000000 : ℝ)] ![(5803589420799/50000000000000 : ℝ), (5671877277071/12500000000000 : ℝ), (21508901463639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1934071047/10000000000 : ℝ)|^4319 ≤ (5803589420799/50000000000000 : ℝ)^3295
        have hw : |(-1934071047/10000000000 : ℝ)|=(1934071047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472462233/10000000000 : ℝ)|^4319 ≤ (5671877277071/12500000000000 : ℝ)^3295
        have hw : |(5472462233/10000000000 : ℝ)|=(5472462233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254208117/10000000000 : ℝ)|^4319 ≤ (21508901463639/50000000000000 : ℝ)^3295
        have hw : |(5254208117/10000000000 : ℝ)|=(5254208117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_13 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538015223/1000000000 : ℝ)*x 0 + (-1030007269/5000000000 : ℝ)*x 1 + (210168321/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538015223/1000000000 : ℝ)^4319 ≤ (8874880961227/20000000000000 : ℝ)^3295 := by
    have hnat : (538015223 : ℕ)^4319*20000000000000^3295 ≤ 8874880961227^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538015223 1000000000 8874880961227 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030007269/5000000000 : ℝ)^4319 ≤ (12607793240387/100000000000000 : ℝ)^3295 := by
    have hnat : (1030007269 : ℕ)^4319*100000000000000^3295 ≤ 12607793240387^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030007269 5000000000 12607793240387 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210168321/400000000 : ℝ)^4319 ≤ (43017801939961/100000000000000 : ℝ)^3295 := by
    have hnat : (210168321 : ℕ)^4319*100000000000000^3295 ≤ 43017801939961^3295*400000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210168321 400000000 43017801939961 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538015223/1000000000 : ℝ), (-1030007269/5000000000 : ℝ), (210168321/400000000 : ℝ)] ![(8874880961227/20000000000000 : ℝ), (12607793240387/100000000000000 : ℝ), (43017801939961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538015223/1000000000 : ℝ)|^4319 ≤ (8874880961227/20000000000000 : ℝ)^3295
        have hw : |(538015223/1000000000 : ℝ)|=(538015223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030007269/5000000000 : ℝ)|^4319 ≤ (12607793240387/100000000000000 : ℝ)^3295
        have hw : |(-1030007269/5000000000 : ℝ)|=(1030007269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210168321/400000000 : ℝ)|^4319 ≤ (43017801939961/100000000000000 : ℝ)^3295
        have hw : |(210168321/400000000 : ℝ)|=(210168321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_14 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269007619/500000000 : ℝ)*x 0 + (5254207029/10000000000 : ℝ)*x 1 + (-515003917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269007619/500000000 : ℝ)^4319 ≤ (8874881285557/20000000000000 : ℝ)^3295 := by
    have hnat : (269007619 : ℕ)^4319*20000000000000^3295 ≤ 8874881285557^3295*500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269007619 500000000 8874881285557 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254207029/10000000000 : ℝ)^4319 ≤ (43017791251183/100000000000000 : ℝ)^3295 := by
    have hnat : (5254207029 : ℕ)^4319*100000000000000^3295 ≤ 43017791251183^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254207029 10000000000 43017791251183 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515003917/2500000000 : ℝ)^4319 ≤ (6303901152769/50000000000000 : ℝ)^3295 := by
    have hnat : (515003917 : ℕ)^4319*50000000000000^3295 ≤ 6303901152769^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515003917 2500000000 6303901152769 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269007619/500000000 : ℝ), (5254207029/10000000000 : ℝ), (-515003917/2500000000 : ℝ)] ![(8874881285557/20000000000000 : ℝ), (43017791251183/100000000000000 : ℝ), (6303901152769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269007619/500000000 : ℝ)|^4319 ≤ (8874881285557/20000000000000 : ℝ)^3295
        have hw : |(269007619/500000000 : ℝ)|=(269007619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254207029/10000000000 : ℝ)|^4319 ≤ (43017791251183/100000000000000 : ℝ)^3295
        have hw : |(5254207029/10000000000 : ℝ)|=(5254207029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515003917/2500000000 : ℝ)|^4319 ≤ (6303901152769/50000000000000 : ℝ)^3295
        have hw : |(-515003917/2500000000 : ℝ)|=(515003917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_box_15 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (829296403/2000000000 : ℝ)*x 0 + (551701591/1250000000 : ℝ)*x 1 + (2206806361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829296403/2000000000 : ℝ)^4319 ≤ (1261608578677/4000000000000 : ℝ)^3295 := by
    have hnat : (829296403 : ℕ)^4319*4000000000000^3295 ≤ 1261608578677^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829296403 2000000000 1261608578677 4000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551701591/1250000000 : ℝ)^4319 ≤ (8557473197823/25000000000000 : ℝ)^3295 := by
    have hnat : (551701591 : ℕ)^4319*25000000000000^3295 ≤ 8557473197823^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551701591 1250000000 8557473197823 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206806361/5000000000 : ℝ)^4319 ≤ (34229892730297/100000000000000 : ℝ)^3295 := by
    have hnat : (2206806361 : ℕ)^4319*100000000000000^3295 ≤ 34229892730297^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206806361 5000000000 34229892730297 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829296403/2000000000 : ℝ), (551701591/1250000000 : ℝ), (2206806361/5000000000 : ℝ)] ![(1261608578677/4000000000000 : ℝ), (8557473197823/25000000000000 : ℝ), (34229892730297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829296403/2000000000 : ℝ)|^4319 ≤ (1261608578677/4000000000000 : ℝ)^3295
        have hw : |(829296403/2000000000 : ℝ)|=(829296403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551701591/1250000000 : ℝ)|^4319 ≤ (8557473197823/25000000000000 : ℝ)^3295
        have hw : |(551701591/1250000000 : ℝ)|=(551701591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206806361/5000000000 : ℝ)|^4319 ≤ (34229892730297/100000000000000 : ℝ)^3295
        have hw : |(2206806361/5000000000 : ℝ)|=(2206806361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31431/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29487/50000 : ℝ) ∧ (80053/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42209/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11189/100000 : ℝ) ^ (2159/512 : ℝ) ≤ (1949736903114999/20000000000000000000 : ℝ) := by
    have hpowers : (11189/100000 : ℝ)^2159 ≤ (1949736903114999/20000000000000000000 : ℝ)^512 := by
      have hnat : (11189 : ℕ)^2159*20000000000000000000^512 ≤ 1949736903114999^512*100000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11189 100000 1949736903114999 20000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11189/100000 : ℝ)) (X := (1949736903114999/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (2159/512 : ℝ) ≤ (3870552790033983/12500000000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^2159 ≤ (3870552790033983/12500000000000000000 : ℝ)^512 := by
      have hnat : (14717 : ℕ)^2159*12500000000000000000^512 ≤ 3870552790033983^512*100000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 3870552790033983 12500000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (3870552790033983/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001949736903114999/10000000000000000000 : ℝ) ≤ (10000462339538563/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (10001949736903114999/10000000000000000000 : ℝ)^512 ≤ (10000462339538563/10000000000000000 : ℝ)^2159 := by
      have hnat : (10001949736903114999 : ℕ)^512*10000000000000000^2159 ≤ 10000462339538563^2159*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001949736903114999 10000000000000000000 10000462339538563 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000462339538563/10000000000000000 : ℝ)) (X := (10001949736903114999/10000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040713106835846859/100000000000000000000 : ℝ) ≤ (10000965348514319/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (100040713106835846859/100000000000000000000 : ℝ)^512 ≤ (10000965348514319/10000000000000000 : ℝ)^2159 := by
      have hnat : (100040713106835846859 : ℕ)^512*10000000000000000^2159 ≤ 10000965348514319^2159*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040713106835846859 100000000000000000000 10000965348514319 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000965348514319/10000000000000000 : ℝ)) (X := (100040713106835846859/100000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253870552790033983/6250000000000000000 : ℝ) ≤ (400058734299603/400000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (6253870552790033983/6250000000000000000 : ℝ)^512 ≤ (400058734299603/400000000000000 : ℝ)^2159 := by
      have hnat : (6253870552790033983 : ℕ)^512*400000000000000^2159 ≤ 400058734299603^2159*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253870552790033983 6250000000000000000 400058734299603 400000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400058734299603/400000000000000 : ℝ)) (X := (6253870552790033983/6250000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1949736903114999/20000000000000000000 : ℝ) ≤ ((157457030352824029/157500000000000000 : ℝ)+2*(17964606277/12600000000000 : ℝ)*(11189/100000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (157457030352824029/157500000000000000 : ℝ)+2*(17964606277/12600000000000 : ℝ)*(11189/100000 : ℝ)=(10000462339538563/10000000000000000 : ℝ) by norm_num, show 1+2*(1949736903114999/20000000000000000000 : ℝ)=(10001949736903114999/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3870552790033983/12500000000000000000 : ℝ)+(1949736903114999/20000000000000000000 : ℝ) ≤ ((157457030352824029/157500000000000000 : ℝ)+(17964606277/12600000000000 : ℝ)*((14717/100000 : ℝ)+(11189/100000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (157457030352824029/157500000000000000 : ℝ)+(17964606277/12600000000000 : ℝ)*((14717/100000 : ℝ)+(11189/100000 : ℝ))=(10000965348514319/10000000000000000 : ℝ) by norm_num, show 1+(3870552790033983/12500000000000000000 : ℝ)+(1949736903114999/20000000000000000000 : ℝ)=(100040713106835846859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3870552790033983/12500000000000000000 : ℝ) ≤ ((157457030352824029/157500000000000000 : ℝ)+2*(17964606277/12600000000000 : ℝ)*(14717/100000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (157457030352824029/157500000000000000 : ℝ)+2*(17964606277/12600000000000 : ℝ)*(14717/100000 : ℝ)=(400058734299603/400000000000000 : ℝ) by norm_num, show 1+2*(3870552790033983/12500000000000000000 : ℝ)=(6253870552790033983/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (157457030352824029/157500000000000000 : ℝ)*(X 1 0+X 2 0)+(17964606277/12600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (157457030352824029/157500000000000000 : ℝ)) (alpha := (17964606277/12600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (157457030352824029/157500000000000000 : ℝ)*(X 0 1+X 2 1)+(17964606277/12600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (157457030352824029/157500000000000000 : ℝ)) (alpha := (17964606277/12600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (157457030352824029/157500000000000000 : ℝ)*(X 0 2+X 1 2)+(17964606277/12600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (157457030352824029/157500000000000000 : ℝ)) (alpha := (17964606277/12600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-931730059/5000000000 : ℝ)*X 0 0+(673653503/1250000000 : ℝ)*X 0 1+(2694614329/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642693319/5000000000 : ℝ)*X 1 0+(-2005810347/10000000000 : ℝ)*X 1 1+(5389227959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285386441/10000000000 : ℝ)*X 2 0+(2694614071/5000000000 : ℝ)*X 2 1+(-401162073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4469993199/10000000000 : ℝ)*X 0 0+(2126074801/5000000000 : ℝ)*X 0 1+(2126074933/5000000000 : ℝ)*X 0 2+(4469993199/10000000000 : ℝ)*X 1 0+(2126074801/5000000000 : ℝ)*X 1 1+(2126074933/5000000000 : ℝ)*X 1 2+(4469993199/10000000000 : ℝ)*X 2 0+(2126074801/5000000000 : ℝ)*X 2 1+(2126074933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219804409/1000000000 : ℝ)*X 0 0+(5265289843/10000000000 : ℝ)*X 0 1+(5265290457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372375331/10000000000 : ℝ)*X 1 0+(-128478791/625000000 : ℝ)*X 1 1+(210611623/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686187509/5000000000 : ℝ)*X 2 0+(2632645417/5000000000 : ℝ)*X 2 1+(-2055660731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4173449329/10000000000 : ℝ)*X 0 0+(4400368497/10000000000 : ℝ)*X 0 1+(275023049/625000000 : ℝ)*X 0 2+(4173449329/10000000000 : ℝ)*X 1 0+(4400368497/10000000000 : ℝ)*X 1 1+(275023049/625000000 : ℝ)*X 1 2+(4173449329/10000000000 : ℝ)*X 2 0+(4400368497/10000000000 : ℝ)*X 2 1+(275023049/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2127737361/10000000000 : ℝ)*X 0 0+(5179887523/10000000000 : ℝ)*X 0 1+(5403241323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637773583/5000000000 : ℝ)*X 1 0+(-2000042773/10000000000 : ℝ)*X 1 1+(1080647999/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318886587/2500000000 : ℝ)*X 2 0+(5403240549/10000000000 : ℝ)*X 2 1+(-500010781/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4502961133/10000000000 : ℝ)*X 0 0+(847075733/2000000000 : ℝ)*X 0 1+(4235378097/10000000000 : ℝ)*X 0 2+(4502961133/10000000000 : ℝ)*X 1 0+(847075733/2000000000 : ℝ)*X 1 1+(4235378097/10000000000 : ℝ)*X 1 2+(4502961133/10000000000 : ℝ)*X 2 0+(847075733/2000000000 : ℝ)*X 2 1+(4235378097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1934071047/10000000000 : ℝ)*X 0 0+(5472462233/10000000000 : ℝ)*X 0 1+(5254208117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538015223/1000000000 : ℝ)*X 1 0+(-1030007269/5000000000 : ℝ)*X 1 1+(210168321/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((269007619/500000000 : ℝ)*X 2 0+(5254207029/10000000000 : ℝ)*X 2 1+(-515003917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((829296403/2000000000 : ℝ)*X 0 0+(551701591/1250000000 : ℝ)*X 0 1+(2206806361/5000000000 : ℝ)*X 0 2+(829296403/2000000000 : ℝ)*X 1 0+(551701591/1250000000 : ℝ)*X 1 1+(2206806361/5000000000 : ℝ)*X 1 2+(829296403/2000000000 : ℝ)*X 2 0+(551701591/1250000000 : ℝ)*X 2 1+(2206806361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31431/50000 : ℝ) ≤ (-137506015239371574213735975591/218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39341021/50000000000000 : ℝ)*(upper1) + (36391967/25000000000000 : ℝ)*(lower4) + (114154471/100000000000000 : ℝ)*(upper5) + (1469809269176337/50000000000000 : ℝ)*(major0) + (1469809269176337/50000000000000 : ℝ)*(major1) + (1469809269176337/50000000000000 : ℝ)*(major2) + (4647204859/100000000000000 : ℝ)*(sp3) + (4008521687295749/100000000000000 : ℝ)*(sp4) + (80168160216453/2000000000000 : ℝ)*(sp5) + (2004216931728567/50000000000000 : ℝ)*(sp6) + (945827764593409/50000000000000 : ℝ)*(sp7) + (42552891/500000000000 : ℝ)*(sp12) + (122187051299/100000000000000 : ℝ)*(sp13) + (19266883363/20000000000000 : ℝ)*(sp14) + (945830088195839/50000000000000 : ℝ)*(f.failure) + (1002132549468487/25000000000000 : ℝ)*(f.sum) + (134879263203/17500000000000000000000000 : ℝ)*base65 + (1059210448837697/875000000000000000000000000000 : ℝ)*base67 + (549156999337697/875000000000000000000000000000 : ℝ)*base69 + (2557817425837697/875000000000000000000000000000 : ℝ)*base71 + (133006696191/35000000000000000000000000 : ℝ)*base73 + (1262823158837697/875000000000000000000000000000 : ℝ)*base75 + (622329992162303/875000000000000000000000000000 : ℝ)*base78 + (1627081612837697/875000000000000000000000000000 : ℝ)*base79 + (272275881141/35000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1930193/500000000000000000000 : ℝ)*base89 + (1930193/500000000000000000000 : ℝ)*base91 + (1930193/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29487/50000 : ℝ) ≤ (16126465397121208460862787983/27343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (4867231/100000000000000 : ℝ)*(lower0) + (10742557/10000000000000 : ℝ)*(lower1) + (13785379/100000000000000 : ℝ)*(lower3) + (59721501/50000000000000 : ℝ)*(lower5) + (94027589634947/3125000000000 : ℝ)*(major0) + (94027589634947/3125000000000 : ℝ)*(major1) + (94027589634947/3125000000000 : ℝ)*(major2) + (2030927571028143/50000000000000 : ℝ)*(sp0) + (1015448335392841/25000000000000 : ℝ)*(sp1) + (406187466598679/10000000000000 : ℝ)*(sp2) + (1936223240843491/100000000000000 : ℝ)*(sp3) + (8900560307/100000000000000 : ℝ)*(sp7) + (40662207713/50000000000000 : ℝ)*(sp9) + (19523930503/100000000000000 : ℝ)*(sp12) + (968116070701899/50000000000000 : ℝ)*(f.failure) + (406187466598679/10000000000000 : ℝ)*(f.sum) + (583379099641/315000000000000000000000000 : ℝ)*base66 + (1561792876263821/164062500000000000000000000000 : ℝ)*base67 + (2564403426137017/328125000000000000000000000000 : ℝ)*base69 + (275497359420071/164062500000000000000000000000 : ℝ)*base71 + (834848712721/315000000000000000000000000 : ℝ)*base74 + (1371781165826321/164062500000000000000000000000 : ℝ)*base75 + (195080530170973/82031250000000000000000000000 : ℝ)*base77 + (1466060098362983/328125000000000000000000000000 : ℝ)*base80 + (93118810891/19687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1145413/500000000000000000000 : ℝ)*base89 + (1145413/500000000000000000000 : ℝ)*base91 + (1145413/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80053/100000 : ℝ) ≤ (43780496544968898458510792477/54687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (154438599/100000000000000 : ℝ)*(upper2) + (21244087/25000000000000 : ℝ)*(lower3) + (2438037/500000000000 : ℝ)*(lower5) + (830066638804147/25000000000000 : ℝ)*(major0) + (830066638804147/25000000000000 : ℝ)*(major1) + (830066638804147/25000000000000 : ℝ)*(major2) + (215241383121/100000000000000 : ℝ)*(sp2) + (43031098367/25000000000000 : ℝ)*(sp3) + (18028143327/100000000000000 : ℝ)*(sp4) + (447720311965851/10000000000000 : ℝ)*(sp8) + (1119309663511131/25000000000000 : ℝ)*(sp9) + (4477023412661403/100000000000000 : ℝ)*(sp10) + (1068218538479123/50000000000000 : ℝ)*(sp11) + (8753121343/50000000000000 : ℝ)*(sp12) + (1068304600675857/50000000000000 : ℝ)*(f.failure) + (1119309663511131/25000000000000 : ℝ)*(f.sum) + (85437932509/157500000000000000000000000 : ℝ)*base65 + (14616555215874421/1312500000000000000000000000000 : ℝ)*base67 + (12470437869249421/1312500000000000000000000000000 : ℝ)*base69 + (614019974686921/1312500000000000000000000000000 : ℝ)*base71 + (247154979391/39375000000000000000000000 : ℝ)*base73 + (224739313813079/1312500000000000000000000000000 : ℝ)*base76 + (2778529847124421/1312500000000000000000000000000 : ℝ)*base77 + (500295890874421/1312500000000000000000000000000 : ℝ)*base79 + (740605042343/315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1408159/500000000000000000000 : ℝ)*base89 + (1408159/500000000000000000000 : ℝ)*base91 + (1408159/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42209/50000 : ℝ) ≤ (-92329599501379747890006881799/109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34729809/12500000000000 : ℝ)*(lower0) + (6084949/20000000000000 : ℝ)*(lower1) + (23507869/100000000000000 : ℝ)*(lower3) + (114581629/25000000000000 : ℝ)*(lower4) + (209809044272991/6250000000000 : ℝ)*(major0) + (209809044272991/6250000000000 : ℝ)*(major1) + (209809044272991/6250000000000 : ℝ)*(major2) + (44276438983/100000000000000 : ℝ)*(sp5) + (144390115287/20000000000000 : ℝ)*(sp6) + (273276635973/100000000000000 : ℝ)*(sp7) + (57272702165139/1250000000000 : ℝ)*(sp12) + (4581771896772137/100000000000000 : ℝ)*(sp13) + (916218844526937/20000000000000 : ℝ)*(sp14) + (1079969255749279/50000000000000 : ℝ)*(sp15) + (540052947033633/25000000000000 : ℝ)*(f.failure) + (57272702165139/1250000000000 : ℝ)*(f.sum) + (89831201417/105000000000000000000000000 : ℝ)*base65 + (57600254217601/27343750000000000000000000000 : ℝ)*base68 + (34629594363971/109375000000000000000000000000 : ℝ)*base69 + (284089989292279/109375000000000000000000000000 : ℝ)*base72 + (204448738997/105000000000000000000000000 : ℝ)*base73 + (65516737979779/109375000000000000000000000000 : ℝ)*base76 + (49025312585363/13671875000000000000000000000 : ℝ)*base78 + (151047938363971/109375000000000000000000000000 : ℝ)*base79 + (1215294775337/105000000000000000000000000 : ℝ)*base81 + (2019471/250000000000000000000 : ℝ)*base89 + (2019471/250000000000000000000 : ℝ)*base91 + (2019471/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1359_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29487/50000 : ℝ) else (80053/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42209/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1359_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1359_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29487/50000 : ℝ) else (80053/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42209/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1359_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1359_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1359_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29487/50000 : ℝ) else (80053/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42209/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1359_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

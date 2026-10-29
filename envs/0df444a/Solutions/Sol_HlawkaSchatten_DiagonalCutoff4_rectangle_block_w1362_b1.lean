-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1362_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:38.814976+00:00
-- url     : https://prove2.me/submissions/d41582c1-a938-4f4d-b987-ce0eba0cb365

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
theorem support_rectangle_w1362_s3_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025251837/10000000000 : ℝ)*x 0 + (5424680217/10000000000 : ℝ)*x 1 + (5233226593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025251837/10000000000 : ℝ)^2161 ≤ (6167609627293/50000000000000 : ℝ)^1649 := by
    have hnat : (2025251837 : ℕ)^2161*50000000000000^1649 ≤ 6167609627293^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025251837 10000000000 6167609627293 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424680217/10000000000 : ℝ)^2161 ≤ (44864171126081/100000000000000 : ℝ)^1649 := by
    have hnat : (5424680217 : ℕ)^2161*100000000000000^1649 ≤ 44864171126081^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424680217 10000000000 44864171126081 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233226593/10000000000 : ℝ)^2161 ≤ (42800609597403/100000000000000 : ℝ)^1649 := by
    have hnat : (5233226593 : ℕ)^2161*100000000000000^1649 ≤ 42800609597403^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233226593 10000000000 42800609597403 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025251837/10000000000 : ℝ), (5424680217/10000000000 : ℝ), (5233226593/10000000000 : ℝ)] ![(6167609627293/50000000000000 : ℝ), (44864171126081/100000000000000 : ℝ), (42800609597403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025251837/10000000000 : ℝ)|^2161 ≤ (6167609627293/50000000000000 : ℝ)^1649
        have hw : |(-2025251837/10000000000 : ℝ)|=(2025251837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424680217/10000000000 : ℝ)|^2161 ≤ (44864171126081/100000000000000 : ℝ)^1649
        have hw : |(5424680217/10000000000 : ℝ)|=(5424680217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233226593/10000000000 : ℝ)|^2161 ≤ (42800609597403/100000000000000 : ℝ)^1649
        have hw : |(5233226593/10000000000 : ℝ)|=(5233226593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351970729/10000000000 : ℝ)*x 0 + (-2123050593/10000000000 : ℝ)*x 1 + (2616613253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351970729/10000000000 : ℝ)^2161 ≤ (1763110862413/4000000000000 : ℝ)^1649 := by
    have hnat : (5351970729 : ℕ)^2161*4000000000000^1649 ≤ 1763110862413^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351970729 10000000000 1763110862413 4000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123050593/10000000000 : ℝ)^2161 ≤ (13121619759899/100000000000000 : ℝ)^1649 := by
    have hnat : (2123050593 : ℕ)^2161*100000000000000^1649 ≤ 13121619759899^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123050593 10000000000 13121619759899 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616613253/5000000000 : ℝ)^2161 ≤ (8560121732987/20000000000000 : ℝ)^1649 := by
    have hnat : (2616613253 : ℕ)^2161*20000000000000^1649 ≤ 8560121732987^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616613253 5000000000 8560121732987 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351970729/10000000000 : ℝ), (-2123050593/10000000000 : ℝ), (2616613253/5000000000 : ℝ)] ![(1763110862413/4000000000000 : ℝ), (13121619759899/100000000000000 : ℝ), (8560121732987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351970729/10000000000 : ℝ)|^2161 ≤ (1763110862413/4000000000000 : ℝ)^1649
        have hw : |(5351970729/10000000000 : ℝ)|=(5351970729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123050593/10000000000 : ℝ)|^2161 ≤ (13121619759899/100000000000000 : ℝ)^1649
        have hw : |(-2123050593/10000000000 : ℝ)|=(2123050593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616613253/5000000000 : ℝ)|^2161 ≤ (8560121732987/20000000000000 : ℝ)^1649
        have hw : |(2616613253/5000000000 : ℝ)|=(2616613253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351970619/10000000000 : ℝ)*x 0 + (5233226673/10000000000 : ℝ)*x 1 + (-1061525259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351970619/10000000000 : ℝ)^2161 ≤ (44077770373101/100000000000000 : ℝ)^1649 := by
    have hnat : (5351970619 : ℕ)^2161*100000000000000^1649 ≤ 44077770373101^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351970619 10000000000 44077770373101 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233226673/10000000000 : ℝ)^2161 ≤ (8560122090969/20000000000000 : ℝ)^1649 := by
    have hnat : (5233226673 : ℕ)^2161*20000000000000^1649 ≤ 8560122090969^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233226673 10000000000 8560122090969 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061525259/5000000000 : ℝ)^2161 ≤ (820101197027/6250000000000 : ℝ)^1649 := by
    have hnat : (1061525259 : ℕ)^2161*6250000000000^1649 ≤ 820101197027^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061525259 5000000000 820101197027 6250000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351970619/10000000000 : ℝ), (5233226673/10000000000 : ℝ), (-1061525259/5000000000 : ℝ)] ![(44077770373101/100000000000000 : ℝ), (8560122090969/20000000000000 : ℝ), (820101197027/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351970619/10000000000 : ℝ)|^2161 ≤ (44077770373101/100000000000000 : ℝ)^1649
        have hw : |(5351970619/10000000000 : ℝ)|=(5351970619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233226673/10000000000 : ℝ)|^2161 ≤ (8560122090969/20000000000000 : ℝ)^1649
        have hw : |(5233226673/10000000000 : ℝ)|=(5233226673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061525259/5000000000 : ℝ)|^2161 ≤ (820101197027/6250000000000 : ℝ)^1649
        have hw : |(-1061525259/5000000000 : ℝ)|=(1061525259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320467549/10000000000 : ℝ)*x 0 + (2061411797/5000000000 : ℝ)*x 1 + (1131714249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320467549/10000000000 : ℝ)^2161 ≤ (33294021025097/100000000000000 : ℝ)^1649 := by
    have hnat : (4320467549 : ℕ)^2161*100000000000000^1649 ≤ 33294021025097^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320467549 10000000000 33294021025097 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061411797/5000000000 : ℝ)^2161 ≤ (626247640819/2000000000000 : ℝ)^1649 := by
    have hnat : (2061411797 : ℕ)^2161*2000000000000^1649 ≤ 626247640819^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061411797 5000000000 626247640819 2000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131714249/2500000000 : ℝ)^2161 ≤ (17696798462197/50000000000000 : ℝ)^1649 := by
    have hnat : (1131714249 : ℕ)^2161*50000000000000^1649 ≤ 17696798462197^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131714249 2500000000 17696798462197 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320467549/10000000000 : ℝ), (2061411797/5000000000 : ℝ), (1131714249/2500000000 : ℝ)] ![(33294021025097/100000000000000 : ℝ), (626247640819/2000000000000 : ℝ), (17696798462197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320467549/10000000000 : ℝ)|^2161 ≤ (33294021025097/100000000000000 : ℝ)^1649
        have hw : |(4320467549/10000000000 : ℝ)|=(4320467549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2061411797/5000000000 : ℝ)|^2161 ≤ (626247640819/2000000000000 : ℝ)^1649
        have hw : |(2061411797/5000000000 : ℝ)|=(2061411797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131714249/2500000000 : ℝ)|^2161 ≤ (17696798462197/50000000000000 : ℝ)^1649
        have hw : |(1131714249/2500000000 : ℝ)|=(1131714249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025270153/10000000000 : ℝ)*x 0 + (163562983/312500000 : ℝ)*x 1 + (2711943291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025270153/10000000000 : ℝ)^2161 ≤ (12335365449813/100000000000000 : ℝ)^1649 := by
    have hnat : (2025270153 : ℕ)^2161*100000000000000^1649 ≤ 12335365449813^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025270153 10000000000 12335365449813 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163562983/312500000 : ℝ)^2161 ≤ (42809064843953/100000000000000 : ℝ)^1649 := by
    have hnat : (163562983 : ℕ)^2161*100000000000000^1649 ≤ 42809064843953^1649*312500000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163562983 312500000 42809064843953 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711943291/5000000000 : ℝ)^2161 ≤ (44855569697931/100000000000000 : ℝ)^1649 := by
    have hnat : (2711943291 : ℕ)^2161*100000000000000^1649 ≤ 44855569697931^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711943291 5000000000 44855569697931 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025270153/10000000000 : ℝ), (163562983/312500000 : ℝ), (2711943291/5000000000 : ℝ)] ![(12335365449813/100000000000000 : ℝ), (42809064843953/100000000000000 : ℝ), (44855569697931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025270153/10000000000 : ℝ)|^2161 ≤ (12335365449813/100000000000000 : ℝ)^1649
        have hw : |(-2025270153/10000000000 : ℝ)|=(2025270153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163562983/312500000 : ℝ)|^2161 ≤ (42809064843953/100000000000000 : ℝ)^1649
        have hw : |(163562983/312500000 : ℝ)|=(163562983/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711943291/5000000000 : ℝ)|^2161 ≤ (44855569697931/100000000000000 : ℝ)^1649
        have hw : |(2711943291/5000000000 : ℝ)|=(2711943291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060508763/2000000000 : ℝ)*x 0 + (-1932390553/10000000000 : ℝ)*x 1 + (5423886981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060508763/2000000000 : ℝ)^2161 ≤ (43545076010917/100000000000000 : ℝ)^1649 := by
    have hnat : (1060508763 : ℕ)^2161*100000000000000^1649 ≤ 43545076010917^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060508763 2000000000 43545076010917 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932390553/10000000000 : ℝ)^2161 ≤ (1449918744327/12500000000000 : ℝ)^1649 := by
    have hnat : (1932390553 : ℕ)^2161*12500000000000^1649 ≤ 1449918744327^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932390553 10000000000 1449918744327 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423886981/10000000000 : ℝ)^2161 ≤ (44855574022201/100000000000000 : ℝ)^1649 := by
    have hnat : (5423886981 : ℕ)^2161*100000000000000^1649 ≤ 44855574022201^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423886981 10000000000 44855574022201 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060508763/2000000000 : ℝ), (-1932390553/10000000000 : ℝ), (5423886981/10000000000 : ℝ)] ![(43545076010917/100000000000000 : ℝ), (1449918744327/12500000000000 : ℝ), (44855574022201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060508763/2000000000 : ℝ)|^2161 ≤ (43545076010917/100000000000000 : ℝ)^1649
        have hw : |(1060508763/2000000000 : ℝ)|=(1060508763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1932390553/10000000000 : ℝ)|^2161 ≤ (1449918744327/12500000000000 : ℝ)^1649
        have hw : |(-1932390553/10000000000 : ℝ)|=(1932390553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423886981/10000000000 : ℝ)|^2161 ≤ (44855574022201/100000000000000 : ℝ)^1649
        have hw : |(5423886981/10000000000 : ℝ)|=(5423886981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662818079/1250000000 : ℝ)*x 0 + (5423886419/10000000000 : ℝ)*x 1 + (-193239021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662818079/1250000000 : ℝ)^2161 ≤ (43545084803389/100000000000000 : ℝ)^1649 := by
    have hnat : (662818079 : ℕ)^2161*100000000000000^1649 ≤ 43545084803389^1649*1250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662818079 1250000000 43545084803389 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423886419/10000000000 : ℝ)^2161 ≤ (358844543451/800000000000 : ℝ)^1649 := by
    have hnat : (5423886419 : ℕ)^2161*800000000000^1649 ≤ 358844543451^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423886419 10000000000 358844543451 800000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193239021/1000000000 : ℝ)^2161 ≤ (579967362823/5000000000000 : ℝ)^1649 := by
    have hnat : (193239021 : ℕ)^2161*5000000000000^1649 ≤ 579967362823^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193239021 1000000000 579967362823 5000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662818079/1250000000 : ℝ), (5423886419/10000000000 : ℝ), (-193239021/1000000000 : ℝ)] ![(43545084803389/100000000000000 : ℝ), (358844543451/800000000000 : ℝ), (579967362823/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662818079/1250000000 : ℝ)|^2161 ≤ (43545084803389/100000000000000 : ℝ)^1649
        have hw : |(662818079/1250000000 : ℝ)|=(662818079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423886419/10000000000 : ℝ)|^2161 ≤ (358844543451/800000000000 : ℝ)^1649
        have hw : |(5423886419/10000000000 : ℝ)|=(5423886419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193239021/1000000000 : ℝ)|^2161 ≤ (579967362823/5000000000000 : ℝ)^1649
        have hw : |(-193239021/1000000000 : ℝ)|=(193239021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s3_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (43205069/100000000 : ℝ)*x 0 + (4525191657/10000000000 : ℝ)*x 1 + (82489957/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43205069/100000000 : ℝ)^2161 ≤ (33294418423393/100000000000000 : ℝ)^1649 := by
    have hnat : (43205069 : ℕ)^2161*100000000000000^1649 ≤ 33294418423393^1649*100000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43205069 100000000 33294418423393 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525191657/10000000000 : ℝ)^2161 ≤ (17688267266829/50000000000000 : ℝ)^1649 := by
    have hnat : (4525191657 : ℕ)^2161*50000000000000^1649 ≤ 17688267266829^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525191657 10000000000 17688267266829 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82489957/200000000 : ℝ)^2161 ≤ (7832261754367/25000000000000 : ℝ)^1649 := by
    have hnat : (82489957 : ℕ)^2161*25000000000000^1649 ≤ 7832261754367^1649*200000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82489957 200000000 7832261754367 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43205069/100000000 : ℝ), (4525191657/10000000000 : ℝ), (82489957/200000000 : ℝ)] ![(33294418423393/100000000000000 : ℝ), (17688267266829/50000000000000 : ℝ), (7832261754367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43205069/100000000 : ℝ)|^2161 ≤ (33294418423393/100000000000000 : ℝ)^1649
        have hw : |(43205069/100000000 : ℝ)|=(43205069/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525191657/10000000000 : ℝ)|^2161 ≤ (17688267266829/50000000000000 : ℝ)^1649
        have hw : |(4525191657/10000000000 : ℝ)|=(4525191657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82489957/200000000 : ℝ)|^2161 ≤ (7832261754367/25000000000000 : ℝ)^1649
        have hw : |(82489957/200000000 : ℝ)|=(82489957/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10939/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14991/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (499/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (499/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (499/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (499/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (499/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (499/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (499/5000 : ℝ) ^ (4321/1024 : ℝ) ≤ (2989334840368423/50000000000000000000 : ℝ) := by
    have hpowers : (499/5000 : ℝ)^4321 ≤ (2989334840368423/50000000000000000000 : ℝ)^1024 := by
      have hnat : (499 : ℕ)^4321*50000000000000000000^1024 ≤ 2989334840368423^1024*5000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        499 5000 2989334840368423 50000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (499/5000 : ℝ)) (X := (2989334840368423/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16027/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (44125929121331337/100000000000000000000 : ℝ) := by
    have hpowers : (16027/100000 : ℝ)^4321 ≤ (44125929121331337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16027 : ℕ)^4321*100000000000000000000^1024 ≤ 44125929121331337^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16027 100000 44125929121331337 100000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16027/100000 : ℝ)) (X := (44125929121331337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002989334840368423/25000000000000000000 : ℝ) ≤ (625017709669319/625000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25002989334840368423/25000000000000000000 : ℝ)^1024 ≤ (625017709669319/625000000000000 : ℝ)^4321 := by
      have hnat : (25002989334840368423 : ℕ)^1024*625000000000000^4321 ≤ 625017709669319^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002989334840368423 25000000000000000000 625017709669319 625000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017709669319/625000000000000 : ℝ)) (X := (25002989334840368423/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050104598802068183/100000000000000000000 : ℝ) ≤ (10001187162798571/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (100050104598802068183/100000000000000000000 : ℝ)^1024 ≤ (10001187162798571/10000000000000000 : ℝ)^4321 := by
      have hnat : (100050104598802068183 : ℕ)^1024*10000000000000000^4321 ≤ 10001187162798571^4321*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050104598802068183 100000000000000000000 10001187162798571 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001187162798571/10000000000000000 : ℝ)) (X := (100050104598802068183/100000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044125929121331337/50000000000000000000 : ℝ) ≤ (5001045485444019/5000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (50044125929121331337/50000000000000000000 : ℝ)^1024 ≤ (5001045485444019/5000000000000000 : ℝ)^4321 := by
      have hnat : (50044125929121331337 : ℕ)^1024*5000000000000000^4321 ≤ 5001045485444019^4321*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044125929121331337 50000000000000000000 5001045485444019 5000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001045485444019/5000000000000000 : ℝ)) (X := (50044125929121331337/50000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2989334840368423/50000000000000000000 : ℝ) ≤ ((7556709179557523821/7558750000000000000 : ℝ)+2*(903808089467/604700000000000 : ℝ)*(499/5000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (7556709179557523821/7558750000000000000 : ℝ)+2*(903808089467/604700000000000 : ℝ)*(499/5000 : ℝ)=(625017709669319/625000000000000 : ℝ) by norm_num, show 1+2*(2989334840368423/50000000000000000000 : ℝ)=(25002989334840368423/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44125929121331337/100000000000000000000 : ℝ)+(2989334840368423/50000000000000000000 : ℝ) ≤ ((7556709179557523821/7558750000000000000 : ℝ)+(903808089467/604700000000000 : ℝ)*((16027/100000 : ℝ)+(499/5000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (7556709179557523821/7558750000000000000 : ℝ)+(903808089467/604700000000000 : ℝ)*((16027/100000 : ℝ)+(499/5000 : ℝ))=(10001187162798571/10000000000000000 : ℝ) by norm_num, show 1+(44125929121331337/100000000000000000000 : ℝ)+(2989334840368423/50000000000000000000 : ℝ)=(100050104598802068183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44125929121331337/100000000000000000000 : ℝ) ≤ ((7556709179557523821/7558750000000000000 : ℝ)+2*(903808089467/604700000000000 : ℝ)*(16027/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (7556709179557523821/7558750000000000000 : ℝ)+2*(903808089467/604700000000000 : ℝ)*(16027/100000 : ℝ)=(5001045485444019/5000000000000000 : ℝ) by norm_num, show 1+2*(44125929121331337/100000000000000000000 : ℝ)=(50044125929121331337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7556709179557523821/7558750000000000000 : ℝ)*(X 1 0+X 2 0)+(903808089467/604700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (499/5000 : ℝ)) (hi := (16027/100000 : ℝ)) (c := (7556709179557523821/7558750000000000000 : ℝ)) (alpha := (903808089467/604700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7556709179557523821/7558750000000000000 : ℝ)*(X 0 1+X 2 1)+(903808089467/604700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (499/5000 : ℝ)) (hi := (16027/100000 : ℝ)) (c := (7556709179557523821/7558750000000000000 : ℝ)) (alpha := (903808089467/604700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7556709179557523821/7558750000000000000 : ℝ)*(X 0 2+X 1 2)+(903808089467/604700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (499/5000 : ℝ)) (hi := (16027/100000 : ℝ)) (c := (7556709179557523821/7558750000000000000 : ℝ)) (alpha := (903808089467/604700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2025251837/10000000000 : ℝ)*X 0 0+(5424680217/10000000000 : ℝ)*X 0 1+(5233226593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351970729/10000000000 : ℝ)*X 1 0+(-2123050593/10000000000 : ℝ)*X 1 1+(2616613253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351970619/10000000000 : ℝ)*X 2 0+(5233226673/10000000000 : ℝ)*X 2 1+(-1061525259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320467549/10000000000 : ℝ)*X 0 0+(2061411797/5000000000 : ℝ)*X 0 1+(1131714249/2500000000 : ℝ)*X 0 2+(4320467549/10000000000 : ℝ)*X 1 0+(2061411797/5000000000 : ℝ)*X 1 1+(1131714249/2500000000 : ℝ)*X 1 2+(4320467549/10000000000 : ℝ)*X 2 0+(2061411797/5000000000 : ℝ)*X 2 1+(1131714249/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025270153/10000000000 : ℝ)*X 0 0+(163562983/312500000 : ℝ)*X 0 1+(2711943291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060508763/2000000000 : ℝ)*X 1 0+(-1932390553/10000000000 : ℝ)*X 1 1+(5423886981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662818079/1250000000 : ℝ)*X 2 0+(5423886419/10000000000 : ℝ)*X 2 1+(-193239021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43205069/100000000 : ℝ)*X 0 0+(4525191657/10000000000 : ℝ)*X 0 1+(82489957/200000000 : ℝ)*X 0 2+(43205069/100000000 : ℝ)*X 1 0+(4525191657/10000000000 : ℝ)*X 1 1+(82489957/200000000 : ℝ)*X 1 2+(43205069/100000000 : ℝ)*X 2 0+(4525191657/10000000000 : ℝ)*X 2 1+(82489957/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1849960761161858158760449989/188968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104341557/5000000000000 : ℝ)*(base19) + (1904827361/100000000000000 : ℝ)*(base23) + (2496993/6250000000000 : ℝ)*(lower2) + (40328753/20000000000000 : ℝ)*(upper3) + (103794863/50000000000000 : ℝ)*(upper5) + (3849178418398703/100000000000000 : ℝ)*(major0) + (3849178418398703/100000000000000 : ℝ)*(major1) + (3849178418398703/100000000000000 : ℝ)*(major2) + (522323563282519/10000000000000 : ℝ)*(sp0) + (1305818190061441/25000000000000 : ℝ)*(sp1) + (5223272942249543/100000000000000 : ℝ)*(sp2) + (2475062264806463/100000000000000 : ℝ)*(sp3) + (7842850343/20000000000000 : ℝ)*(sp4) + (19398588339/100000000000000 : ℝ)*(sp7) + (1237540831697401/50000000000000 : ℝ)*(f.failure) + (652909355884613/12500000000000 : ℝ)*(f.sum) + (99513771986269/30235000000000000000000000000 : ℝ)*base66 + (7536788721098858337/755875000000000000000000000000000 : ℝ)*base68 + (3462284657711483337/755875000000000000000000000000000 : ℝ)*base70 + (1689794174313358337/755875000000000000000000000000000 : ℝ)*base72 + (75976161443277/15117500000000000000000000000 : ℝ)*base74 + (1233779805067483337/755875000000000000000000000000000 : ℝ)*base76 + (2748752835865766663/755875000000000000000000000000000 : ℝ)*base77 + (925064809966733337/755875000000000000000000000000000 : ℝ)*base80 + (87620869869339/30235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (20021829/5000000000000000000000 : ℝ)*base89 + (20021829/5000000000000000000000 : ℝ)*base91 + (20021829/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1433886489275925403231821/23621093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (385726221/100000000000000 : ℝ)*(base19) + (1658271963/100000000000000 : ℝ)*(base23) + (190277711/100000000000000 : ℝ)*(upper3) + (74115377/50000000000000 : ℝ)*(lower4) + (3432903/2500000000000 : ℝ)*(upper5) + (970300729603707/25000000000000 : ℝ)*(major0) + (970300729603707/25000000000000 : ℝ)*(major1) + (970300729603707/25000000000000 : ℝ)*(major2) + (5149928689/50000000000000 : ℝ)*(sp1) + (1488684041/5000000000000 : ℝ)*(sp2) + (5266731919207541/100000000000000 : ℝ)*(sp4) + (2633360616811971/50000000000000 : ℝ)*(sp5) + (2633350243627379/50000000000000 : ℝ)*(sp6) + (38994904931229/1562500000000 : ℝ)*(sp7) + (38994904931229/1562500000000 : ℝ)*(f.failure) + (5266731919207541/100000000000000 : ℝ)*(f.sum) + (17790222489331/30235000000000000000000000000 : ℝ)*base65 + (76520983271516947/188968750000000000000000000000000 : ℝ)*base67 + (252576029540954447/188968750000000000000000000000000 : ℝ)*base69 + (2200573762234391947/188968750000000000000000000000000 : ℝ)*base71 + (25477273225661/7558750000000000000000000000 : ℝ)*base74 + (1132535713798920553/188968750000000000000000000000000 : ℝ)*base76 + (1075363243697891947/188968750000000000000000000000000 : ℝ)*base77 + (349809479697295553/188968750000000000000000000000000 : ℝ)*base80 + (9570898200839/1889687500000000000000000000 : ℝ)*base82 + (894441/156250000000000000000 : ℝ)*base89 + (894441/156250000000000000000 : ℝ)*base91 + (894441/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1362_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14991/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1362_s4_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026562327/10000000000 : ℝ)*x 0 + (5413894239/10000000000 : ℝ)*x 1 + (2621575627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026562327/10000000000 : ℝ)^2161 ≤ (12345680400981/100000000000000 : ℝ)^1649 := by
    have hnat : (2026562327 : ℕ)^2161*100000000000000^1649 ≤ 12345680400981^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026562327 10000000000 12345680400981 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413894239/10000000000 : ℝ)^2161 ≤ (44747305979209/100000000000000 : ℝ)^1649 := by
    have hnat : (5413894239 : ℕ)^2161*100000000000000^1649 ≤ 44747305979209^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413894239 10000000000 44747305979209 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621575627/5000000000 : ℝ)^2161 ≤ (8581402721587/20000000000000 : ℝ)^1649 := by
    have hnat : (2621575627 : ℕ)^2161*20000000000000^1649 ≤ 8581402721587^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621575627 5000000000 8581402721587 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026562327/10000000000 : ℝ), (5413894239/10000000000 : ℝ), (2621575627/5000000000 : ℝ)] ![(12345680400981/100000000000000 : ℝ), (44747305979209/100000000000000 : ℝ), (8581402721587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026562327/10000000000 : ℝ)|^2161 ≤ (12345680400981/100000000000000 : ℝ)^1649
        have hw : |(-2026562327/10000000000 : ℝ)|=(2026562327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413894239/10000000000 : ℝ)|^2161 ≤ (44747305979209/100000000000000 : ℝ)^1649
        have hw : |(5413894239/10000000000 : ℝ)|=(5413894239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621575627/5000000000 : ℝ)|^2161 ≤ (8581402721587/20000000000000 : ℝ)^1649
        have hw : |(2621575627/5000000000 : ℝ)|=(2621575627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674605911/5000000000 : ℝ)*x 0 + (-422716749/2000000000 : ℝ)*x 1 + (1310787663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674605911/5000000000 : ℝ)^2161 ≤ (11011999302203/25000000000000 : ℝ)^1649 := by
    have hnat : (2674605911 : ℕ)^2161*25000000000000^1649 ≤ 11011999302203^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674605911 5000000000 11011999302203 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422716749/2000000000 : ℝ)^2161 ≤ (13044995628243/100000000000000 : ℝ)^1649 := by
    have hnat : (422716749 : ℕ)^2161*100000000000000^1649 ≤ 13044995628243^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422716749 2000000000 13044995628243 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310787663/2500000000 : ℝ)^2161 ≤ (42907007151891/100000000000000 : ℝ)^1649 := by
    have hnat : (1310787663 : ℕ)^2161*100000000000000^1649 ≤ 42907007151891^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310787663 2500000000 42907007151891 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674605911/5000000000 : ℝ), (-422716749/2000000000 : ℝ), (1310787663/2500000000 : ℝ)] ![(11011999302203/25000000000000 : ℝ), (13044995628243/100000000000000 : ℝ), (42907007151891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674605911/5000000000 : ℝ)|^2161 ≤ (11011999302203/25000000000000 : ℝ)^1649
        have hw : |(2674605911/5000000000 : ℝ)|=(2674605911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422716749/2000000000 : ℝ)|^2161 ≤ (13044995628243/100000000000000 : ℝ)^1649
        have hw : |(-422716749/2000000000 : ℝ)|=(422716749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310787663/2500000000 : ℝ)|^2161 ≤ (42907007151891/100000000000000 : ℝ)^1649
        have hw : |(1310787663/2500000000 : ℝ)|=(1310787663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674606157/5000000000 : ℝ)*x 0 + (5243150917/10000000000 : ℝ)*x 1 + (-1056791369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674606157/5000000000 : ℝ)^2161 ≤ (11012000629523/25000000000000 : ℝ)^1649 := by
    have hnat : (2674606157 : ℕ)^2161*25000000000000^1649 ≤ 11012000629523^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674606157 5000000000 11012000629523 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243150917/10000000000 : ℝ)^2161 ≤ (42907009993837/100000000000000 : ℝ)^1649 := by
    have hnat : (5243150917 : ℕ)^2161*100000000000000^1649 ≤ 42907009993837^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243150917 10000000000 42907009993837 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056791369/5000000000 : ℝ)^2161 ≤ (130449874833/1000000000000 : ℝ)^1649 := by
    have hnat : (1056791369 : ℕ)^2161*1000000000000^1649 ≤ 130449874833^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056791369 5000000000 130449874833 1000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674606157/5000000000 : ℝ), (5243150917/10000000000 : ℝ), (-1056791369/5000000000 : ℝ)] ![(11012000629523/25000000000000 : ℝ), (42907009993837/100000000000000 : ℝ), (130449874833/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674606157/5000000000 : ℝ)|^2161 ≤ (11012000629523/25000000000000 : ℝ)^1649
        have hw : |(2674606157/5000000000 : ℝ)|=(2674606157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243150917/10000000000 : ℝ)|^2161 ≤ (42907009993837/100000000000000 : ℝ)^1649
        have hw : |(5243150917/10000000000 : ℝ)|=(5243150917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056791369/5000000000 : ℝ)|^2161 ≤ (130449874833/1000000000000 : ℝ)^1649
        have hw : |(-1056791369/5000000000 : ℝ)|=(1056791369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1080315481/2500000000 : ℝ)*x 0 + (4144580111/10000000000 : ℝ)*x 1 + (900981227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080315481/2500000000 : ℝ)^2161 ≤ (33302043485401/100000000000000 : ℝ)^1649 := by
    have hnat : (1080315481 : ℕ)^2161*100000000000000^1649 ≤ 33302043485401^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080315481 2500000000 33302043485401 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144580111/10000000000 : ℝ)^2161 ≤ (31529102570819/100000000000000 : ℝ)^1649 := by
    have hnat : (4144580111 : ℕ)^2161*100000000000000^1649 ≤ 31529102570819^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144580111 10000000000 31529102570819 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900981227/2000000000 : ℝ)^2161 ≤ (17584426961869/50000000000000 : ℝ)^1649 := by
    have hnat : (900981227 : ℕ)^2161*50000000000000^1649 ≤ 17584426961869^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900981227 2000000000 17584426961869 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080315481/2500000000 : ℝ), (4144580111/10000000000 : ℝ), (900981227/2000000000 : ℝ)] ![(33302043485401/100000000000000 : ℝ), (31529102570819/100000000000000 : ℝ), (17584426961869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080315481/2500000000 : ℝ)|^2161 ≤ (33302043485401/100000000000000 : ℝ)^1649
        have hw : |(1080315481/2500000000 : ℝ)|=(1080315481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144580111/10000000000 : ℝ)|^2161 ≤ (31529102570819/100000000000000 : ℝ)^1649
        have hw : |(4144580111/10000000000 : ℝ)|=(4144580111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900981227/2000000000 : ℝ)|^2161 ≤ (17584426961869/50000000000000 : ℝ)^1649
        have hw : |(900981227/2000000000 : ℝ)|=(900981227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-506643859/2500000000 : ℝ)*x 0 + (163868093/312500000 : ℝ)*x 1 + (2706631523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506643859/2500000000 : ℝ)^2161 ≤ (12345785055787/100000000000000 : ℝ)^1649 := by
    have hnat : (506643859 : ℕ)^2161*100000000000000^1649 ≤ 12345785055787^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506643859 2500000000 12345785055787 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163868093/312500000 : ℝ)^2161 ≤ (8582749125701/20000000000000 : ℝ)^1649 := by
    have hnat : (163868093 : ℕ)^2161*20000000000000^1649 ≤ 8582749125701^1649*312500000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163868093 312500000 8582749125701 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706631523/5000000000 : ℝ)^2161 ≤ (22370234647261/50000000000000 : ℝ)^1649 := by
    have hnat : (2706631523 : ℕ)^2161*50000000000000^1649 ≤ 22370234647261^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706631523 5000000000 22370234647261 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506643859/2500000000 : ℝ), (163868093/312500000 : ℝ), (2706631523/5000000000 : ℝ)] ![(12345785055787/100000000000000 : ℝ), (8582749125701/20000000000000 : ℝ), (22370234647261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506643859/2500000000 : ℝ)|^2161 ≤ (12345785055787/100000000000000 : ℝ)^1649
        have hw : |(-506643859/2500000000 : ℝ)|=(506643859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163868093/312500000 : ℝ)|^2161 ≤ (8582749125701/20000000000000 : ℝ)^1649
        have hw : |(163868093/312500000 : ℝ)|=(163868093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706631523/5000000000 : ℝ)|^2161 ≤ (22370234647261/50000000000000 : ℝ)^1649
        have hw : |(2706631523/5000000000 : ℝ)|=(2706631523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652566609/5000000000 : ℝ)*x 0 + (-1943470567/10000000000 : ℝ)*x 1 + (2706631479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652566609/5000000000 : ℝ)^2161 ≤ (21786472508001/50000000000000 : ℝ)^1649 := by
    have hnat : (2652566609 : ℕ)^2161*50000000000000^1649 ≤ 21786472508001^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652566609 5000000000 21786472508001 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943470567/10000000000 : ℝ)^2161 ≤ (1460823327967/12500000000000 : ℝ)^1649 := by
    have hnat : (1943470567 : ℕ)^2161*12500000000000^1649 ≤ 1460823327967^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943470567 10000000000 1460823327967 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706631479/5000000000 : ℝ)^2161 ≤ (44740468341379/100000000000000 : ℝ)^1649 := by
    have hnat : (2706631479 : ℕ)^2161*100000000000000^1649 ≤ 44740468341379^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706631479 5000000000 44740468341379 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652566609/5000000000 : ℝ), (-1943470567/10000000000 : ℝ), (2706631479/5000000000 : ℝ)] ![(21786472508001/50000000000000 : ℝ), (1460823327967/12500000000000 : ℝ), (44740468341379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652566609/5000000000 : ℝ)|^2161 ≤ (21786472508001/50000000000000 : ℝ)^1649
        have hw : |(2652566609/5000000000 : ℝ)|=(2652566609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1943470567/10000000000 : ℝ)|^2161 ≤ (1460823327967/12500000000000 : ℝ)^1649
        have hw : |(-1943470567/10000000000 : ℝ)|=(1943470567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706631479/5000000000 : ℝ)|^2161 ≤ (44740468341379/100000000000000 : ℝ)^1649
        have hw : |(2706631479/5000000000 : ℝ)|=(2706631479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530513307/1000000000 : ℝ)*x 0 + (5413263199/10000000000 : ℝ)*x 1 + (-1943470439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530513307/1000000000 : ℝ)^2161 ≤ (43572943422999/100000000000000 : ℝ)^1649 := by
    have hnat : (530513307 : ℕ)^2161*100000000000000^1649 ≤ 43572943422999^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530513307 1000000000 43572943422999 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413263199/10000000000 : ℝ)^2161 ≤ (11185117737923/25000000000000 : ℝ)^1649 := by
    have hnat : (5413263199 : ℕ)^2161*25000000000000^1649 ≤ 11185117737923^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413263199 10000000000 11185117737923 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943470439/10000000000 : ℝ)^2161 ≤ (2337317123011/20000000000000 : ℝ)^1649 := by
    have hnat : (1943470439 : ℕ)^2161*20000000000000^1649 ≤ 2337317123011^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943470439 10000000000 2337317123011 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530513307/1000000000 : ℝ), (5413263199/10000000000 : ℝ), (-1943470439/10000000000 : ℝ)] ![(43572943422999/100000000000000 : ℝ), (11185117737923/25000000000000 : ℝ), (2337317123011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530513307/1000000000 : ℝ)|^2161 ≤ (43572943422999/100000000000000 : ℝ)^1649
        have hw : |(530513307/1000000000 : ℝ)|=(530513307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413263199/10000000000 : ℝ)|^2161 ≤ (11185117737923/25000000000000 : ℝ)^1649
        have hw : |(5413263199/10000000000 : ℝ)|=(5413263199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1943470439/10000000000 : ℝ)|^2161 ≤ (2337317123011/20000000000000 : ℝ)^1649
        have hw : |(-1943470439/10000000000 : ℝ)|=(1943470439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s4_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864258109/2000000000 : ℝ)*x 0 + (45035809/100000000 : ℝ)*x 1 + (2072955487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864258109/2000000000 : ℝ)^2161 ≤ (4162791567481/12500000000000 : ℝ)^1649 := by
    have hnat : (864258109 : ℕ)^2161*12500000000000^1649 ≤ 4162791567481^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864258109 2000000000 4162791567481 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45035809/100000000 : ℝ)^2161 ≤ (35155296422831/100000000000000 : ℝ)^1649 := by
    have hnat : (45035809 : ℕ)^2161*100000000000000^1649 ≤ 35155296422831^1649*100000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45035809 100000000 35155296422831 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072955487/5000000000 : ℝ)^2161 ≤ (31542371020477/100000000000000 : ℝ)^1649 := by
    have hnat : (2072955487 : ℕ)^2161*100000000000000^1649 ≤ 31542371020477^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072955487 5000000000 31542371020477 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864258109/2000000000 : ℝ), (45035809/100000000 : ℝ), (2072955487/5000000000 : ℝ)] ![(4162791567481/12500000000000 : ℝ), (35155296422831/100000000000000 : ℝ), (31542371020477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864258109/2000000000 : ℝ)|^2161 ≤ (4162791567481/12500000000000 : ℝ)^1649
        have hw : |(864258109/2000000000 : ℝ)|=(864258109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45035809/100000000 : ℝ)|^2161 ≤ (35155296422831/100000000000000 : ℝ)^1649
        have hw : |(45035809/100000000 : ℝ)|=(45035809/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072955487/5000000000 : ℝ)|^2161 ≤ (31542371020477/100000000000000 : ℝ)^1649
        have hw : |(2072955487/5000000000 : ℝ)|=(2072955487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11151/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10939/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (8805384925350261/100000000000000000000 : ℝ) := by
    have hpowers : (10939/100000 : ℝ)^4321 ≤ (8805384925350261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10939 : ℕ)^4321*100000000000000000000^1024 ≤ 8805384925350261^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10939 100000 8805384925350261 100000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10939/100000 : ℝ)) (X := (8805384925350261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14991/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (33283616426319127/100000000000000000000 : ℝ) := by
    have hpowers : (14991/100000 : ℝ)^4321 ≤ (33283616426319127/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14991 : ℕ)^4321*100000000000000000000^1024 ≤ 33283616426319127^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14991 100000 33283616426319127 100000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14991/100000 : ℝ)) (X := (33283616426319127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008805384925350261/50000000000000000000 : ℝ) ≤ (10000417315826123/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (50008805384925350261/50000000000000000000 : ℝ)^1024 ≤ (10000417315826123/10000000000000000 : ℝ)^4321 := by
      have hnat : (50008805384925350261 : ℕ)^1024*10000000000000000^4321 ≤ 10000417315826123^4321*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008805384925350261 50000000000000000000 10000417315826123 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417315826123/10000000000000000 : ℝ)) (X := (50008805384925350261/50000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010522250337917347/25000000000000000000 : ℝ) ≤ (500049863710397/500000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25010522250337917347/25000000000000000000 : ℝ)^1024 ≤ (500049863710397/500000000000000 : ℝ)^4321 := by
      have hnat : (25010522250337917347 : ℕ)^1024*500000000000000^4321 ≤ 500049863710397^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010522250337917347 25000000000000000000 500049863710397 500000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500049863710397/500000000000000 : ℝ)) (X := (25010522250337917347/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033283616426319127/50000000000000000000 : ℝ) ≤ (10001577232589757/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (50033283616426319127/50000000000000000000 : ℝ)^1024 ≤ (10001577232589757/10000000000000000 : ℝ)^4321 := by
      have hnat : (50033283616426319127 : ℕ)^1024*10000000000000000^4321 ≤ 10001577232589757^4321*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033283616426319127 50000000000000000000 10001577232589757 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001577232589757/10000000000000000 : ℝ)) (X := (50033283616426319127/50000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8805384925350261/100000000000000000000 : ℝ) ≤ ((4050900263425005807/4052000000000000000 : ℝ)+2*(579958381817/405200000000000 : ℝ)*(10939/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (4050900263425005807/4052000000000000000 : ℝ)+2*(579958381817/405200000000000 : ℝ)*(10939/100000 : ℝ)=(10000417315826123/10000000000000000 : ℝ) by norm_num, show 1+2*(8805384925350261/100000000000000000000 : ℝ)=(50008805384925350261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33283616426319127/100000000000000000000 : ℝ)+(8805384925350261/100000000000000000000 : ℝ) ≤ ((4050900263425005807/4052000000000000000 : ℝ)+(579958381817/405200000000000 : ℝ)*((14991/100000 : ℝ)+(10939/100000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (4050900263425005807/4052000000000000000 : ℝ)+(579958381817/405200000000000 : ℝ)*((14991/100000 : ℝ)+(10939/100000 : ℝ))=(500049863710397/500000000000000 : ℝ) by norm_num, show 1+(33283616426319127/100000000000000000000 : ℝ)+(8805384925350261/100000000000000000000 : ℝ)=(25010522250337917347/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33283616426319127/100000000000000000000 : ℝ) ≤ ((4050900263425005807/4052000000000000000 : ℝ)+2*(579958381817/405200000000000 : ℝ)*(14991/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (4050900263425005807/4052000000000000000 : ℝ)+2*(579958381817/405200000000000 : ℝ)*(14991/100000 : ℝ)=(10001577232589757/10000000000000000 : ℝ) by norm_num, show 1+2*(33283616426319127/100000000000000000000 : ℝ)=(50033283616426319127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4050900263425005807/4052000000000000000 : ℝ)*(X 1 0+X 2 0)+(579958381817/405200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14991/100000 : ℝ)) (c := (4050900263425005807/4052000000000000000 : ℝ)) (alpha := (579958381817/405200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4050900263425005807/4052000000000000000 : ℝ)*(X 0 1+X 2 1)+(579958381817/405200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14991/100000 : ℝ)) (c := (4050900263425005807/4052000000000000000 : ℝ)) (alpha := (579958381817/405200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4050900263425005807/4052000000000000000 : ℝ)*(X 0 2+X 1 2)+(579958381817/405200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14991/100000 : ℝ)) (c := (4050900263425005807/4052000000000000000 : ℝ)) (alpha := (579958381817/405200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2026562327/10000000000 : ℝ)*X 0 0+(5413894239/10000000000 : ℝ)*X 0 1+(2621575627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674605911/5000000000 : ℝ)*X 1 0+(-422716749/2000000000 : ℝ)*X 1 1+(1310787663/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674606157/5000000000 : ℝ)*X 2 0+(5243150917/10000000000 : ℝ)*X 2 1+(-1056791369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080315481/2500000000 : ℝ)*X 0 0+(4144580111/10000000000 : ℝ)*X 0 1+(900981227/2000000000 : ℝ)*X 0 2+(1080315481/2500000000 : ℝ)*X 1 0+(4144580111/10000000000 : ℝ)*X 1 1+(900981227/2000000000 : ℝ)*X 1 2+(1080315481/2500000000 : ℝ)*X 2 0+(4144580111/10000000000 : ℝ)*X 2 1+(900981227/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-506643859/2500000000 : ℝ)*X 0 0+(163868093/312500000 : ℝ)*X 0 1+(2706631523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652566609/5000000000 : ℝ)*X 1 0+(-1943470567/10000000000 : ℝ)*X 1 1+(2706631479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530513307/1000000000 : ℝ)*X 2 0+(5413263199/10000000000 : ℝ)*X 2 1+(-1943470439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864258109/2000000000 : ℝ)*X 0 0+(45035809/100000000 : ℝ)*X 0 1+(2072955487/5000000000 : ℝ)*X 0 2+(864258109/2000000000 : ℝ)*X 1 0+(45035809/100000000 : ℝ)*X 1 1+(2072955487/5000000000 : ℝ)*X 1 2+(864258109/2000000000 : ℝ)*X 2 0+(45035809/100000000 : ℝ)*X 2 1+(2072955487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9220784021724102054273/633125000000000000000000000 : ℝ) := by norm_num
    linear_combination (184438361/100000000000000 : ℝ)*(base19) + (168257051/25000000000000 : ℝ)*(base23) + (10067397/10000000000000 : ℝ)*(lower3) + (158261917/100000000000000 : ℝ)*(upper4) + (1079007180535479/25000000000000 : ℝ)*(major0) + (1079007180535479/25000000000000 : ℝ)*(major1) + (1079007180535479/25000000000000 : ℝ)*(major2) + (5856763105632731/100000000000000 : ℝ)*(sp0) + (2928376635290903/50000000000000 : ℝ)*(sp1) + (2928391303590343/50000000000000 : ℝ)*(sp2) + (693816964148679/25000000000000 : ℝ)*(sp3) + (20174576159/100000000000000 : ℝ)*(sp4) + (29825188723/100000000000000 : ℝ)*(sp5) + (2911008053/50000000000000 : ℝ)*(sp7) + (1387636839305411/50000000000000 : ℝ)*(f.failure) + (585678328020889/10000000000000 : ℝ)*(f.sum) + (9709474559601/2532500000000000000000000000 : ℝ)*base66 + (506649904501743447/101300000000000000000000000000000 : ℝ)*base68 + (913393135238356553/101300000000000000000000000000000 : ℝ)*base69 + (77288206452043447/101300000000000000000000000000000 : ℝ)*base72 + (5972896272559/2532500000000000000000000000 : ℝ)*base73 + (1937531560732956553/101300000000000000000000000000000 : ℝ)*base75 + (794443244612556553/101300000000000000000000000000000 : ℝ)*base77 + (658581586321443447/101300000000000000000000000000000 : ℝ)*base80 + (7505945750997/5065000000000000000000000000 : ℝ)*base82 + (3426119/5000000000000000000000 : ℝ)*base89 + (3426119/5000000000000000000000 : ℝ)*base91 + (3426119/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (654023343301212092326090209/101300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (196658689/20000000000000 : ℝ)*(base19) + (974592117/100000000000000 : ℝ)*(base23) + (52642843/100000000000000 : ℝ)*(upper3) + (13124473/25000000000000 : ℝ)*(lower4) + (21038493/100000000000000 : ℝ)*(upper5) + (2174032541814971/50000000000000 : ℝ)*(major0) + (2174032541814971/50000000000000 : ℝ)*(major1) + (2174032541814971/50000000000000 : ℝ)*(major2) + (4073141499/20000000000000 : ℝ)*(sp1) + (27218913507/100000000000000 : ℝ)*(sp2) + (590025639412401/10000000000000 : ℝ)*(sp4) + (5900235045123071/100000000000000 : ℝ)*(sp5) + (2950114100309193/50000000000000 : ℝ)*(sp6) + (1397936778962909/50000000000000 : ℝ)*(sp7) + (1397936778962909/50000000000000 : ℝ)*(f.failure) + (590025639412401/10000000000000 : ℝ)*(f.sum) + (37925366136193/10130000000000000000000000000 : ℝ)*base66 + (413264067921606597/202600000000000000000000000000000 : ℝ)*base67 + (74145183681593403/202600000000000000000000000000000 : ℝ)*base70 + (322523738354806597/202600000000000000000000000000000 : ℝ)*base71 + (47238721800467/10130000000000000000000000000 : ℝ)*base73 + (3066892879656393403/202600000000000000000000000000000 : ℝ)*base76 + (2175164621544806597/202600000000000000000000000000000 : ℝ)*base77 + (742995775991806597/202600000000000000000000000000000 : ℝ)*base79 + (33589935442253/10130000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1459161/5000000000000000000000 : ℝ)*base89 + (1459161/5000000000000000000000 : ℝ)*base91 + (1459161/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1362_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1362_s5_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026779697/10000000000 : ℝ)*x 0 + (5412000801/10000000000 : ℝ)*x 1 + (2622450807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026779697/10000000000 : ℝ)^2161 ≤ (3086853946669/25000000000000 : ℝ)^1649 := by
    have hnat : (2026779697 : ℕ)^2161*25000000000000^1649 ≤ 3086853946669^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026779697 10000000000 3086853946669 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412000801/10000000000 : ℝ)^2161 ≤ (2236339909739/5000000000000 : ℝ)^1649 := by
    have hnat : (5412000801 : ℕ)^2161*5000000000000^1649 ≤ 2236339909739^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412000801 10000000000 2236339909739 5000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622450807/5000000000 : ℝ)^2161 ≤ (42925786012223/100000000000000 : ℝ)^1649 := by
    have hnat : (2622450807 : ℕ)^2161*100000000000000^1649 ≤ 42925786012223^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622450807 5000000000 42925786012223 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026779697/10000000000 : ℝ), (5412000801/10000000000 : ℝ), (2622450807/5000000000 : ℝ)] ![(3086853946669/25000000000000 : ℝ), (2236339909739/5000000000000 : ℝ), (42925786012223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026779697/10000000000 : ℝ)|^2161 ≤ (3086853946669/25000000000000 : ℝ)^1649
        have hw : |(-2026779697/10000000000 : ℝ)|=(2026779697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412000801/10000000000 : ℝ)|^2161 ≤ (2236339909739/5000000000000 : ℝ)^1649
        have hw : |(5412000801/10000000000 : ℝ)|=(5412000801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622450807/5000000000 : ℝ)|^2161 ≤ (42925786012223/100000000000000 : ℝ)^1649
        have hw : |(2622450807/5000000000 : ℝ)|=(2622450807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069745473/2000000000 : ℝ)*x 0 + (-2111908181/10000000000 : ℝ)*x 1 + (2622450797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069745473/2000000000 : ℝ)^2161 ≤ (44042769401027/100000000000000 : ℝ)^1649 := by
    have hnat : (1069745473 : ℕ)^2161*100000000000000^1649 ≤ 44042769401027^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069745473 2000000000 44042769401027 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111908181/10000000000 : ℝ)^2161 ≤ (325786119761/2500000000000 : ℝ)^1649 := by
    have hnat : (2111908181 : ℕ)^2161*2500000000000^1649 ≤ 325786119761^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111908181 10000000000 325786119761 2500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622450797/5000000000 : ℝ)^2161 ≤ (8585157159543/20000000000000 : ℝ)^1649 := by
    have hnat : (2622450797 : ℕ)^2161*20000000000000^1649 ≤ 8585157159543^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622450797 5000000000 8585157159543 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069745473/2000000000 : ℝ), (-2111908181/10000000000 : ℝ), (2622450797/5000000000 : ℝ)] ![(44042769401027/100000000000000 : ℝ), (325786119761/2500000000000 : ℝ), (8585157159543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069745473/2000000000 : ℝ)|^2161 ≤ (44042769401027/100000000000000 : ℝ)^1649
        have hw : |(1069745473/2000000000 : ℝ)|=(1069745473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111908181/10000000000 : ℝ)|^2161 ≤ (325786119761/2500000000000 : ℝ)^1649
        have hw : |(-2111908181/10000000000 : ℝ)|=(2111908181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622450797/5000000000 : ℝ)|^2161 ≤ (8585157159543/20000000000000 : ℝ)^1649
        have hw : |(2622450797/5000000000 : ℝ)|=(2622450797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348727389/10000000000 : ℝ)*x 0 + (2622450793/5000000000 : ℝ)*x 1 + (-6599713/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348727389/10000000000 : ℝ)^2161 ≤ (44042769660009/100000000000000 : ℝ)^1649 := by
    have hnat : (5348727389 : ℕ)^2161*100000000000000^1649 ≤ 44042769660009^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348727389 10000000000 44042769660009 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622450793/5000000000 : ℝ)^2161 ≤ (42925785711911/100000000000000 : ℝ)^1649 := by
    have hnat : (2622450793 : ℕ)^2161*100000000000000^1649 ≤ 42925785711911^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622450793 5000000000 42925785711911 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6599713/31250000 : ℝ)^2161 ≤ (13031444620627/100000000000000 : ℝ)^1649 := by
    have hnat : (6599713 : ℕ)^2161*100000000000000^1649 ≤ 13031444620627^1649*31250000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6599713 31250000 13031444620627 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348727389/10000000000 : ℝ), (2622450793/5000000000 : ℝ), (-6599713/31250000 : ℝ)] ![(44042769660009/100000000000000 : ℝ), (42925785711911/100000000000000 : ℝ), (13031444620627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348727389/10000000000 : ℝ)|^2161 ≤ (44042769660009/100000000000000 : ℝ)^1649
        have hw : |(5348727389/10000000000 : ℝ)|=(5348727389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622450793/5000000000 : ℝ)|^2161 ≤ (42925785711911/100000000000000 : ℝ)^1649
        have hw : |(2622450793/5000000000 : ℝ)|=(2622450793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6599713/31250000 : ℝ)|^2161 ≤ (13031444620627/100000000000000 : ℝ)^1649
        have hw : |(-6599713/31250000 : ℝ)|=(6599713/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (540174279/1250000000 : ℝ)*x 0 + (1037101951/2500000000 : ℝ)*x 1 + (450104459/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540174279/1250000000 : ℝ)^2161 ≤ (3330337971957/10000000000000 : ℝ)^1649 := by
    have hnat : (540174279 : ℕ)^2161*10000000000000^1649 ≤ 3330337971957^1649*1250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540174279 1250000000 3330337971957 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037101951/2500000000 : ℝ)^2161 ≤ (7891816876511/25000000000000 : ℝ)^1649 := by
    have hnat : (1037101951 : ℕ)^2161*25000000000000^1649 ≤ 7891816876511^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037101951 2500000000 7891816876511 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450104459/1000000000 : ℝ)^2161 ≤ (8782338190417/25000000000000 : ℝ)^1649 := by
    have hnat : (450104459 : ℕ)^2161*25000000000000^1649 ≤ 8782338190417^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450104459 1000000000 8782338190417 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540174279/1250000000 : ℝ), (1037101951/2500000000 : ℝ), (450104459/1000000000 : ℝ)] ![(3330337971957/10000000000000 : ℝ), (7891816876511/25000000000000 : ℝ), (8782338190417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540174279/1250000000 : ℝ)|^2161 ≤ (3330337971957/10000000000000 : ℝ)^1649
        have hw : |(540174279/1250000000 : ℝ)|=(540174279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037101951/2500000000 : ℝ)|^2161 ≤ (7891816876511/25000000000000 : ℝ)^1649
        have hw : |(1037101951/2500000000 : ℝ)|=(1037101951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450104459/1000000000 : ℝ)|^2161 ≤ (8782338190417/25000000000000 : ℝ)^1649
        have hw : |(450104459/1000000000 : ℝ)|=(450104459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026791849/10000000000 : ℝ)*x 0 + (5245503037/10000000000 : ℝ)*x 1 + (2705698113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026791849/10000000000 : ℝ)^2161 ≤ (12347512804561/100000000000000 : ℝ)^1649 := by
    have hnat : (2026791849 : ℕ)^2161*100000000000000^1649 ≤ 12347512804561^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026791849 10000000000 12347512804561 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245503037/10000000000 : ℝ)^2161 ≤ (10733059162981/25000000000000 : ℝ)^1649 := by
    have hnat : (5245503037 : ℕ)^2161*25000000000000^1649 ≤ 10733059162981^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245503037 10000000000 10733059162981 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705698113/5000000000 : ℝ)^2161 ≤ (44720250525707/100000000000000 : ℝ)^1649 := by
    have hnat : (2705698113 : ℕ)^2161*100000000000000^1649 ≤ 44720250525707^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705698113 5000000000 44720250525707 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026791849/10000000000 : ℝ), (5245503037/10000000000 : ℝ), (2705698113/5000000000 : ℝ)] ![(12347512804561/100000000000000 : ℝ), (10733059162981/25000000000000 : ℝ), (44720250525707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026791849/10000000000 : ℝ)|^2161 ≤ (12347512804561/100000000000000 : ℝ)^1649
        have hw : |(-2026791849/10000000000 : ℝ)|=(2026791849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245503037/10000000000 : ℝ)|^2161 ≤ (10733059162981/25000000000000 : ℝ)^1649
        have hw : |(5245503037/10000000000 : ℝ)|=(5245503037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705698113/5000000000 : ℝ)|^2161 ≤ (44720250525707/100000000000000 : ℝ)^1649
        have hw : |(2705698113/5000000000 : ℝ)|=(2705698113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652794419/5000000000 : ℝ)*x 0 + (-972706767/5000000000 : ℝ)*x 1 + (2705698117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652794419/5000000000 : ℝ)^2161 ≤ (43577849160989/100000000000000 : ℝ)^1649 := by
    have hnat : (2652794419 : ℕ)^2161*100000000000000^1649 ≤ 43577849160989^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652794419 5000000000 43577849160989 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972706767/5000000000 : ℝ)^2161 ≤ (1170190020031/10000000000000 : ℝ)^1649 := by
    have hnat : (972706767 : ℕ)^2161*10000000000000^1649 ≤ 1170190020031^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972706767 5000000000 1170190020031 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705698117/5000000000 : ℝ)^2161 ≤ (44720250612347/100000000000000 : ℝ)^1649 := by
    have hnat : (2705698117 : ℕ)^2161*100000000000000^1649 ≤ 44720250612347^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705698117 5000000000 44720250612347 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652794419/5000000000 : ℝ), (-972706767/5000000000 : ℝ), (2705698117/5000000000 : ℝ)] ![(43577849160989/100000000000000 : ℝ), (1170190020031/10000000000000 : ℝ), (44720250612347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652794419/5000000000 : ℝ)|^2161 ≤ (43577849160989/100000000000000 : ℝ)^1649
        have hw : |(2652794419/5000000000 : ℝ)|=(2652794419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972706767/5000000000 : ℝ)|^2161 ≤ (1170190020031/10000000000000 : ℝ)^1649
        have hw : |(-972706767/5000000000 : ℝ)|=(972706767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705698117/5000000000 : ℝ)|^2161 ≤ (44720250612347/100000000000000 : ℝ)^1649
        have hw : |(2705698117/5000000000 : ℝ)|=(2705698117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652794431/5000000000 : ℝ)*x 0 + (2705698099/5000000000 : ℝ)*x 1 + (-121588347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652794431/5000000000 : ℝ)^2161 ≤ (43577849419321/100000000000000 : ℝ)^1649 := by
    have hnat : (2652794431 : ℕ)^2161*100000000000000^1649 ≤ 43577849419321^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652794431 5000000000 43577849419321 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705698099/5000000000 : ℝ)^2161 ≤ (44720250222467/100000000000000 : ℝ)^1649 := by
    have hnat : (2705698099 : ℕ)^2161*100000000000000^1649 ≤ 44720250222467^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705698099 5000000000 44720250222467 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121588347/625000000 : ℝ)^2161 ≤ (11701900342199/100000000000000 : ℝ)^1649 := by
    have hnat : (121588347 : ℕ)^2161*100000000000000^1649 ≤ 11701900342199^1649*625000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121588347 625000000 11701900342199 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652794431/5000000000 : ℝ), (2705698099/5000000000 : ℝ), (-121588347/625000000 : ℝ)] ![(43577849419321/100000000000000 : ℝ), (44720250222467/100000000000000 : ℝ), (11701900342199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652794431/5000000000 : ℝ)|^2161 ≤ (43577849419321/100000000000000 : ℝ)^1649
        have hw : |(2652794431/5000000000 : ℝ)|=(2652794431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705698099/5000000000 : ℝ)|^2161 ≤ (44720250222467/100000000000000 : ℝ)^1649
        have hw : |(2705698099/5000000000 : ℝ)|=(2705698099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121588347/625000000 : ℝ)|^2161 ≤ (11701900342199/100000000000000 : ℝ)^1649
        have hw : |(-121588347/625000000 : ℝ)|=(121588347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s5_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4321419817/10000000000 : ℝ)*x 0 + (224988767/500000000 : ℝ)*x 1 + (4149683587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321419817/10000000000 : ℝ)^2161 ≤ (33303638114717/100000000000000 : ℝ)^1649 := by
    have hnat : (4321419817 : ℕ)^2161*100000000000000^1649 ≤ 33303638114717^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321419817 10000000000 33303638114717 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224988767/500000000 : ℝ)^2161 ≤ (35116371434303/100000000000000 : ℝ)^1649 := by
    have hnat : (224988767 : ℕ)^2161*100000000000000^1649 ≤ 35116371434303^1649*500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224988767 500000000 35116371434303 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149683587/10000000000 : ℝ)^2161 ≤ (631599808759/2000000000000 : ℝ)^1649 := by
    have hnat : (4149683587 : ℕ)^2161*2000000000000^1649 ≤ 631599808759^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149683587 10000000000 631599808759 2000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321419817/10000000000 : ℝ), (224988767/500000000 : ℝ), (4149683587/10000000000 : ℝ)] ![(33303638114717/100000000000000 : ℝ), (35116371434303/100000000000000 : ℝ), (631599808759/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321419817/10000000000 : ℝ)|^2161 ≤ (33303638114717/100000000000000 : ℝ)^1649
        have hw : |(4321419817/10000000000 : ℝ)|=(4321419817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224988767/500000000 : ℝ)|^2161 ≤ (35116371434303/100000000000000 : ℝ)^1649
        have hw : |(224988767/500000000 : ℝ)|=(224988767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149683587/10000000000 : ℝ)|^2161 ≤ (631599808759/2000000000000 : ℝ)^1649
        have hw : |(4149683587/10000000000 : ℝ)|=(4149683587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11189/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7363/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11151/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (4774136227392397/50000000000000000000 : ℝ) := by
    have hpowers : (11151/100000 : ℝ)^4321 ≤ (4774136227392397/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11151 : ℕ)^4321*50000000000000000000^1024 ≤ 4774136227392397^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11151 100000 4774136227392397 50000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11151/100000 : ℝ)) (X := (4774136227392397/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (4321/1024 : ℝ) ≤ (7806501541487671/25000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^4321 ≤ (7806501541487671/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7383 : ℕ)^4321*25000000000000000000^1024 ≤ 7806501541487671^1024*50000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 7806501541487671 25000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (7806501541487671/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004774136227392397/25000000000000000000 : ℝ) ≤ (5000226260558637/5000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25004774136227392397/25000000000000000000 : ℝ)^1024 ≤ (5000226260558637/5000000000000000 : ℝ)^4321 := by
      have hnat : (25004774136227392397 : ℕ)^1024*5000000000000000^4321 ≤ 5000226260558637^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004774136227392397 25000000000000000000 5000226260558637 5000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000226260558637/5000000000000000 : ℝ)) (X := (25004774136227392397/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020387139310367739/50000000000000000000 : ℝ) ≤ (10000966127468007/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (50020387139310367739/50000000000000000000 : ℝ)^1024 ≤ (10000966127468007/10000000000000000 : ℝ)^4321 := by
      have hnat : (50020387139310367739 : ℕ)^1024*10000000000000000^4321 ≤ 10000966127468007^4321*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020387139310367739 50000000000000000000 10000966127468007 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000966127468007/10000000000000000 : ℝ)) (X := (50020387139310367739/50000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507806501541487671/12500000000000000000 : ℝ) ≤ (500073986690937/500000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (12507806501541487671/12500000000000000000 : ℝ)^1024 ≤ (500073986690937/500000000000000 : ℝ)^4321 := by
      have hnat : (12507806501541487671 : ℕ)^1024*500000000000000^4321 ≤ 500073986690937^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507806501541487671 12500000000000000000 500073986690937 500000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500073986690937/500000000000000 : ℝ)) (X := (12507806501541487671/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4774136227392397/50000000000000000000 : ℝ) ≤ ((376460223072967689/376562500000000000 : ℝ)+2*(171202116911/120500000000000 : ℝ)*(11151/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (376460223072967689/376562500000000000 : ℝ)+2*(171202116911/120500000000000 : ℝ)*(11151/100000 : ℝ)=(5000226260558637/5000000000000000 : ℝ) by norm_num, show 1+2*(4774136227392397/50000000000000000000 : ℝ)=(25004774136227392397/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7806501541487671/25000000000000000000 : ℝ)+(4774136227392397/50000000000000000000 : ℝ) ≤ ((376460223072967689/376562500000000000 : ℝ)+(171202116911/120500000000000 : ℝ)*((7383/50000 : ℝ)+(11151/100000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (376460223072967689/376562500000000000 : ℝ)+(171202116911/120500000000000 : ℝ)*((7383/50000 : ℝ)+(11151/100000 : ℝ))=(10000966127468007/10000000000000000 : ℝ) by norm_num, show 1+(7806501541487671/25000000000000000000 : ℝ)+(4774136227392397/50000000000000000000 : ℝ)=(50020387139310367739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7806501541487671/25000000000000000000 : ℝ) ≤ ((376460223072967689/376562500000000000 : ℝ)+2*(171202116911/120500000000000 : ℝ)*(7383/50000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (376460223072967689/376562500000000000 : ℝ)+2*(171202116911/120500000000000 : ℝ)*(7383/50000 : ℝ)=(500073986690937/500000000000000 : ℝ) by norm_num, show 1+2*(7806501541487671/25000000000000000000 : ℝ)=(12507806501541487671/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (376460223072967689/376562500000000000 : ℝ)*(X 1 0+X 2 0)+(171202116911/120500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (376460223072967689/376562500000000000 : ℝ)) (alpha := (171202116911/120500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (376460223072967689/376562500000000000 : ℝ)*(X 0 1+X 2 1)+(171202116911/120500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (376460223072967689/376562500000000000 : ℝ)) (alpha := (171202116911/120500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (376460223072967689/376562500000000000 : ℝ)*(X 0 2+X 1 2)+(171202116911/120500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (376460223072967689/376562500000000000 : ℝ)) (alpha := (171202116911/120500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2026779697/10000000000 : ℝ)*X 0 0+(5412000801/10000000000 : ℝ)*X 0 1+(2622450807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069745473/2000000000 : ℝ)*X 1 0+(-2111908181/10000000000 : ℝ)*X 1 1+(2622450797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348727389/10000000000 : ℝ)*X 2 0+(2622450793/5000000000 : ℝ)*X 2 1+(-6599713/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540174279/1250000000 : ℝ)*X 0 0+(1037101951/2500000000 : ℝ)*X 0 1+(450104459/1000000000 : ℝ)*X 0 2+(540174279/1250000000 : ℝ)*X 1 0+(1037101951/2500000000 : ℝ)*X 1 1+(450104459/1000000000 : ℝ)*X 1 2+(540174279/1250000000 : ℝ)*X 2 0+(1037101951/2500000000 : ℝ)*X 2 1+(450104459/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2026791849/10000000000 : ℝ)*X 0 0+(5245503037/10000000000 : ℝ)*X 0 1+(2705698113/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652794419/5000000000 : ℝ)*X 1 0+(-972706767/5000000000 : ℝ)*X 1 1+(2705698117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652794431/5000000000 : ℝ)*X 2 0+(2705698099/5000000000 : ℝ)*X 2 1+(-121588347/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321419817/10000000000 : ℝ)*X 0 0+(224988767/500000000 : ℝ)*X 0 1+(4149683587/10000000000 : ℝ)*X 0 2+(4321419817/10000000000 : ℝ)*X 1 0+(224988767/500000000 : ℝ)*X 1 1+(4149683587/10000000000 : ℝ)*X 1 2+(4321419817/10000000000 : ℝ)*X 2 0+(224988767/500000000 : ℝ)*X 2 1+(4149683587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68264160199574241627842331/18828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (612475827/100000000000000 : ℝ)*(base19) + (58646179/10000000000000 : ℝ)*(base23) + (5655397/20000000000000 : ℝ)*(lower2) + (12841813/20000000000000 : ℝ)*(upper3) + (28038757/50000000000000 : ℝ)*(upper5) + (551267830560593/12500000000000 : ℝ)*(major0) + (551267830560593/12500000000000 : ℝ)*(major1) + (551267830560593/12500000000000 : ℝ)*(major2) + (1196896370984729/20000000000000 : ℝ)*(sp0) + (1196898831879203/20000000000000 : ℝ)*(sp1) + (5984494185410053/100000000000000 : ℝ)*(sp2) + (708946117993987/25000000000000 : ℝ)*(sp3) + (6458474099/50000000000000 : ℝ)*(sp4) + (5924266737/100000000000000 : ℝ)*(sp7) + (708947599060671/25000000000000 : ℝ)*(f.failure) + (2992247385935921/50000000000000 : ℝ)*(f.sum) + (4150430941417/3012500000000000000000000000 : ℝ)*base65 + (157823321733708933/18828125000000000000000000000000 : ℝ)*base67 + (43034833941990183/18828125000000000000000000000000 : ℝ)*base69 + (58892439025673327/4707031250000000000000000000000 : ℝ)*base71 + (10359726937359/6025000000000000000000000000 : ℝ)*base73 + (51530382706677683/18828125000000000000000000000000 : ℝ)*base75 + (48360016128612279/9414062500000000000000000000000 : ℝ)*base77 + (162456503524393529/9414062500000000000000000000000 : ℝ)*base79 + (28180206209691/6025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (43199341/2500000000000000000000 : ℝ)*base90 + (43199341/2500000000000000000000 : ℝ)*base92 + (43199341/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8985627031794367319543121/4707031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (94447469/25000000000000 : ℝ)*(base19) + (399461623/100000000000000 : ℝ)*(base23) + (101127/25000000000000 : ℝ)*(upper2) + (10402873/25000000000000 : ℝ)*(upper3) + (50516357/100000000000000 : ℝ)*(upper5) + (2221092381496099/50000000000000 : ℝ)*(major0) + (2221092381496099/50000000000000 : ℝ)*(major1) + (2221092381496099/50000000000000 : ℝ)*(major2) + (4101143797/50000000000000 : ℝ)*(sp1) + (1855067421/25000000000000 : ℝ)*(sp2) + (376748467808807/6250000000000 : ℝ)*(sp4) + (3013983452431721/50000000000000 : ℝ)*(sp5) + (1205593533041921/20000000000000 : ℝ)*(sp6) + (2856393977410823/100000000000000 : ℝ)*(sp7) + (2856393977410823/100000000000000 : ℝ)*(f.failure) + (376748467808807/6250000000000 : ℝ)*(f.sum) + (24108301914803/6025000000000000000000000000 : ℝ)*base65 + (6139186379615833/2353515625000000000000000000000 : ℝ)*base68 + (48852902602995211/18828125000000000000000000000000 : ℝ)*base69 + (104642719669870211/18828125000000000000000000000000 : ℝ)*base71 + (4574245166143/1506250000000000000000000000 : ℝ)*base74 + (167864542758879789/18828125000000000000000000000000 : ℝ)*base76 + (60522315327682711/18828125000000000000000000000000 : ℝ)*base77 + (108484189650677293/9414062500000000000000000000000 : ℝ)*base79 + (4483547811853/6025000000000000000000000000 : ℝ)*base81 + (12430533/10000000000000000000000 : ℝ)*base90 + (12430533/10000000000000000000000 : ℝ)*base92 + (12430533/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1362_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1362_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1362_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1362_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1362_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1362_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

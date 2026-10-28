-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:54:58.505136+00:00
-- url     : https://prove2.me/submissions/5d25c458-3f03-4d63-b1ba-fc513194ab8b

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
theorem support_rectangle_w1262_s3_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054052621/5000000000 : ℝ)*x 0 + (1354481611/2500000000 : ℝ)*x 1 + (655266723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054052621/5000000000 : ℝ)^8455 ≤ (12816640405283/100000000000000 : ℝ)^6407 := by
    have hnat : (1054052621 : ℕ)^8455*100000000000000^6407 ≤ 12816640405283^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054052621 5000000000 12816640405283 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354481611/2500000000 : ℝ)^8455 ≤ (11135065174629/25000000000000 : ℝ)^6407 := by
    have hnat : (1354481611 : ℕ)^8455*25000000000000^6407 ≤ 11135065174629^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354481611 2500000000 11135065174629 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655266723/1250000000 : ℝ)^8455 ≤ (21321549437507/50000000000000 : ℝ)^6407 := by
    have hnat : (655266723 : ℕ)^8455*50000000000000^6407 ≤ 21321549437507^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655266723 1250000000 21321549437507 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054052621/5000000000 : ℝ), (1354481611/2500000000 : ℝ), (655266723/1250000000 : ℝ)] ![(12816640405283/100000000000000 : ℝ), (11135065174629/25000000000000 : ℝ), (21321549437507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054052621/5000000000 : ℝ)|^8455 ≤ (12816640405283/100000000000000 : ℝ)^6407
        have hw : |(-1054052621/5000000000 : ℝ)|=(1054052621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354481611/2500000000 : ℝ)|^8455 ≤ (11135065174629/25000000000000 : ℝ)^6407
        have hw : |(1354481611/2500000000 : ℝ)|=(1354481611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655266723/1250000000 : ℝ)|^8455 ≤ (21321549437507/50000000000000 : ℝ)^6407
        have hw : |(655266723/1250000000 : ℝ)|=(655266723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675525293/5000000000 : ℝ)*x 0 + (-439550313/2000000000 : ℝ)*x 1 + (524213389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675525293/5000000000 : ℝ)^8455 ≤ (43816178500801/100000000000000 : ℝ)^6407 := by
    have hnat : (2675525293 : ℕ)^8455*100000000000000^6407 ≤ 43816178500801^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675525293 5000000000 43816178500801 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439550313/2000000000 : ℝ)^8455 ≤ (13540721481763/100000000000000 : ℝ)^6407 := by
    have hnat : (439550313 : ℕ)^8455*100000000000000^6407 ≤ 13540721481763^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439550313 2000000000 13540721481763 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524213389/1000000000 : ℝ)^8455 ≤ (42643100012917/100000000000000 : ℝ)^6407 := by
    have hnat : (524213389 : ℕ)^8455*100000000000000^6407 ≤ 42643100012917^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524213389 1000000000 42643100012917 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675525293/5000000000 : ℝ), (-439550313/2000000000 : ℝ), (524213389/1000000000 : ℝ)] ![(43816178500801/100000000000000 : ℝ), (13540721481763/100000000000000 : ℝ), (42643100012917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675525293/5000000000 : ℝ)|^8455 ≤ (43816178500801/100000000000000 : ℝ)^6407
        have hw : |(2675525293/5000000000 : ℝ)|=(2675525293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-439550313/2000000000 : ℝ)|^8455 ≤ (13540721481763/100000000000000 : ℝ)^6407
        have hw : |(-439550313/2000000000 : ℝ)|=(439550313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524213389/1000000000 : ℝ)|^8455 ≤ (42643100012917/100000000000000 : ℝ)^6407
        have hw : |(524213389/1000000000 : ℝ)|=(524213389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070210113/2000000000 : ℝ)*x 0 + (5242134367/10000000000 : ℝ)*x 1 + (-2197750961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070210113/2000000000 : ℝ)^8455 ≤ (43816178273881/100000000000000 : ℝ)^6407 := by
    have hnat : (1070210113 : ℕ)^8455*100000000000000^6407 ≤ 43816178273881^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070210113 2000000000 43816178273881 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242134367/10000000000 : ℝ)^8455 ≤ (42643105133483/100000000000000 : ℝ)^6407 := by
    have hnat : (5242134367 : ℕ)^8455*100000000000000^6407 ≤ 42643105133483^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242134367 10000000000 42643105133483 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197750961/10000000000 : ℝ)^8455 ≤ (13540716570887/100000000000000 : ℝ)^6407 := by
    have hnat : (2197750961 : ℕ)^8455*100000000000000^6407 ≤ 13540716570887^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197750961 10000000000 13540716570887 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070210113/2000000000 : ℝ), (5242134367/10000000000 : ℝ), (-2197750961/10000000000 : ℝ)] ![(43816178273881/100000000000000 : ℝ), (42643105133483/100000000000000 : ℝ), (13540716570887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070210113/2000000000 : ℝ)|^8455 ≤ (43816178273881/100000000000000 : ℝ)^6407
        have hw : |(1070210113/2000000000 : ℝ)|=(1070210113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242134367/10000000000 : ℝ)|^8455 ≤ (42643105133483/100000000000000 : ℝ)^6407
        have hw : |(5242134367/10000000000 : ℝ)|=(5242134367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197750961/10000000000 : ℝ)|^8455 ≤ (13540716570887/100000000000000 : ℝ)^6407
        have hw : |(-2197750961/10000000000 : ℝ)|=(2197750961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346433579/10000000000 : ℝ)*x 0 + (4171005173/10000000000 : ℝ)*x 1 + (1132247207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346433579/10000000000 : ℝ)^8455 ≤ (3330137283019/10000000000000 : ℝ)^6407 := by
    have hnat : (4346433579 : ℕ)^8455*10000000000000^6407 ≤ 3330137283019^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346433579 10000000000 3330137283019 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171005173/10000000000 : ℝ)^8455 ≤ (7884797439509/25000000000000 : ℝ)^6407 := by
    have hnat : (4171005173 : ℕ)^8455*25000000000000^6407 ≤ 7884797439509^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171005173 10000000000 7884797439509 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132247207/2500000000 : ℝ)^8455 ≤ (17579718702311/50000000000000 : ℝ)^6407 := by
    have hnat : (1132247207 : ℕ)^8455*50000000000000^6407 ≤ 17579718702311^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132247207 2500000000 17579718702311 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346433579/10000000000 : ℝ), (4171005173/10000000000 : ℝ), (1132247207/2500000000 : ℝ)] ![(3330137283019/10000000000000 : ℝ), (7884797439509/25000000000000 : ℝ), (17579718702311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346433579/10000000000 : ℝ)|^8455 ≤ (3330137283019/10000000000000 : ℝ)^6407
        have hw : |(4346433579/10000000000 : ℝ)|=(4346433579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171005173/10000000000 : ℝ)|^8455 ≤ (7884797439509/25000000000000 : ℝ)^6407
        have hw : |(4171005173/10000000000 : ℝ)|=(4171005173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132247207/2500000000 : ℝ)|^8455 ≤ (17579718702311/50000000000000 : ℝ)^6407
        have hw : |(1132247207/2500000000 : ℝ)|=(1132247207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108119223/10000000000 : ℝ)*x 0 + (2621382411/5000000000 : ℝ)*x 1 + (5417291661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108119223/10000000000 : ℝ)^8455 ≤ (200261759/1562500000 : ℝ)^6407 := by
    have hnat : (2108119223 : ℕ)^8455*1562500000^6407 ≤ 200261759^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108119223 10000000000 200261759 1562500000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621382411/5000000000 : ℝ)^8455 ≤ (2665617072451/6250000000000 : ℝ)^6407 := by
    have hnat : (2621382411 : ℕ)^8455*6250000000000^6407 ≤ 2665617072451^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621382411 5000000000 2665617072451 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417291661/10000000000 : ℝ)^8455 ≤ (44533374243851/100000000000000 : ℝ)^6407 := by
    have hnat : (5417291661 : ℕ)^8455*100000000000000^6407 ≤ 44533374243851^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417291661 10000000000 44533374243851 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108119223/10000000000 : ℝ), (2621382411/5000000000 : ℝ), (5417291661/10000000000 : ℝ)] ![(200261759/1562500000 : ℝ), (2665617072451/6250000000000 : ℝ), (44533374243851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108119223/10000000000 : ℝ)|^8455 ≤ (200261759/1562500000 : ℝ)^6407
        have hw : |(-2108119223/10000000000 : ℝ)|=(2108119223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621382411/5000000000 : ℝ)|^8455 ≤ (2665617072451/6250000000000 : ℝ)^6407
        have hw : |(2621382411/5000000000 : ℝ)|=(2621382411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417291661/10000000000 : ℝ)|^8455 ≤ (44533374243851/100000000000000 : ℝ)^6407
        have hw : |(5417291661/10000000000 : ℝ)|=(5417291661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2653071341/5000000000 : ℝ)*x 0 + (-12641207/62500000 : ℝ)*x 1 + (10834583/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653071341/5000000000 : ℝ)^8455 ≤ (1354111490749/3125000000000 : ℝ)^6407 := by
    have hnat : (2653071341 : ℕ)^8455*3125000000000^6407 ≤ 1354111490749^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653071341 5000000000 1354111490749 3125000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12641207/62500000 : ℝ)^8455 ≤ (758441236803/6250000000000 : ℝ)^6407 := by
    have hnat : (12641207 : ℕ)^8455*6250000000000^6407 ≤ 758441236803^6407*62500000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12641207 62500000 758441236803 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10834583/20000000 : ℝ)^8455 ≤ (5566671562159/12500000000000 : ℝ)^6407 := by
    have hnat : (10834583 : ℕ)^8455*12500000000000^6407 ≤ 5566671562159^6407*20000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10834583 20000000 5566671562159 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653071341/5000000000 : ℝ), (-12641207/62500000 : ℝ), (10834583/20000000 : ℝ)] ![(1354111490749/3125000000000 : ℝ), (758441236803/6250000000000 : ℝ), (5566671562159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653071341/5000000000 : ℝ)|^8455 ≤ (1354111490749/3125000000000 : ℝ)^6407
        have hw : |(2653071341/5000000000 : ℝ)|=(2653071341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12641207/62500000 : ℝ)|^8455 ≤ (758441236803/6250000000000 : ℝ)^6407
        have hw : |(-12641207/62500000 : ℝ)|=(12641207/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10834583/20000000 : ℝ)|^8455 ≤ (5566671562159/12500000000000 : ℝ)^6407
        have hw : |(10834583/20000000 : ℝ)|=(10834583/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265307101/500000000 : ℝ)*x 0 + (1083458389/2000000000 : ℝ)*x 1 + (-2022593411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265307101/500000000 : ℝ)^8455 ≤ (43331560569817/100000000000000 : ℝ)^6407 := by
    have hnat : (265307101 : ℕ)^8455*100000000000000^6407 ≤ 43331560569817^6407*500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265307101 500000000 43331560569817 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083458389/2000000000 : ℝ)^8455 ≤ (11133344331193/25000000000000 : ℝ)^6407 := by
    have hnat : (1083458389 : ℕ)^8455*25000000000000^6407 ≤ 11133344331193^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083458389 2000000000 11133344331193 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022593411/10000000000 : ℝ)^8455 ≤ (12135062092863/100000000000000 : ℝ)^6407 := by
    have hnat : (2022593411 : ℕ)^8455*100000000000000^6407 ≤ 12135062092863^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022593411 10000000000 12135062092863 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265307101/500000000 : ℝ), (1083458389/2000000000 : ℝ), (-2022593411/10000000000 : ℝ)] ![(43331560569817/100000000000000 : ℝ), (11133344331193/25000000000000 : ℝ), (12135062092863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265307101/500000000 : ℝ)|^8455 ≤ (43331560569817/100000000000000 : ℝ)^6407
        have hw : |(265307101/500000000 : ℝ)|=(265307101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083458389/2000000000 : ℝ)|^8455 ≤ (11133344331193/25000000000000 : ℝ)^6407
        have hw : |(1083458389/2000000000 : ℝ)|=(1083458389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2022593411/10000000000 : ℝ)|^8455 ≤ (12135062092863/100000000000000 : ℝ)^6407
        have hw : |(-2022593411/10000000000 : ℝ)|=(2022593411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s3_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346461433/10000000000 : ℝ)*x 0 + (2263851503/5000000000 : ℝ)*x 1 + (208614847/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346461433/10000000000 : ℝ)^8455 ≤ (6660330891659/20000000000000 : ℝ)^6407 := by
    have hnat : (4346461433 : ℕ)^8455*20000000000000^6407 ≤ 6660330891659^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346461433 10000000000 6660330891659 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263851503/5000000000 : ℝ)^8455 ≤ (3514626513233/10000000000000 : ℝ)^6407 := by
    have hnat : (2263851503 : ℕ)^8455*10000000000000^6407 ≤ 3514626513233^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263851503 5000000000 3514626513233 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208614847/500000000 : ℝ)^8455 ≤ (1972005024677/6250000000000 : ℝ)^6407 := by
    have hnat : (208614847 : ℕ)^8455*6250000000000^6407 ≤ 1972005024677^6407*500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208614847 500000000 1972005024677 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346461433/10000000000 : ℝ), (2263851503/5000000000 : ℝ), (208614847/500000000 : ℝ)] ![(6660330891659/20000000000000 : ℝ), (3514626513233/10000000000000 : ℝ), (1972005024677/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346461433/10000000000 : ℝ)|^8455 ≤ (6660330891659/20000000000000 : ℝ)^6407
        have hw : |(4346461433/10000000000 : ℝ)|=(4346461433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263851503/5000000000 : ℝ)|^8455 ≤ (3514626513233/10000000000000 : ℝ)^6407
        have hw : |(2263851503/5000000000 : ℝ)|=(2263851503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208614847/500000000 : ℝ)|^8455 ≤ (1972005024677/6250000000000 : ℝ)^6407
        have hw : |(208614847/500000000 : ℝ)|=(208614847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5481/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (479/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16171/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (479/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (479/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16171/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (479/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (479/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16171/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (479/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (479/5000 : ℝ) ^ (4227/1024 : ℝ) ≤ (779935084848109/12500000000000000000 : ℝ) := by
    have hpowers : (479/5000 : ℝ)^4227 ≤ (779935084848109/12500000000000000000 : ℝ)^1024 := by
      have hnat : (479 : ℕ)^4227*12500000000000000000^1024 ≤ 779935084848109^1024*5000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        479 5000 779935084848109 12500000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (479/5000 : ℝ)) (X := (779935084848109/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16171/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (54165338855779477/100000000000000000000 : ℝ) := by
    have hpowers : (16171/100000 : ℝ)^4227 ≤ (54165338855779477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16171 : ℕ)^4227*100000000000000000000^1024 ≤ 54165338855779477^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16171 100000 54165338855779477 100000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16171/100000 : ℝ)) (X := (54165338855779477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250779935084848109/6250000000000000000 : ℝ) ≤ (2000060458255571/2000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (6250779935084848109/6250000000000000000 : ℝ)^1024 ≤ (2000060458255571/2000000000000000 : ℝ)^4227 := by
      have hnat : (6250779935084848109 : ℕ)^1024*2000000000000000^4227 ≤ 2000060458255571^4227*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250779935084848109 6250000000000000000 2000060458255571 2000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000060458255571/2000000000000000 : ℝ)) (X := (6250779935084848109/6250000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060404819534564349/100000000000000000000 : ℝ) ≤ (10001462985197541/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (100060404819534564349/100000000000000000000 : ℝ)^1024 ≤ (10001462985197541/10000000000000000 : ℝ)^4227 := by
      have hnat : (100060404819534564349 : ℕ)^1024*10000000000000000^4227 ≤ 10001462985197541^4227*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060404819534564349 100000000000000000000 10001462985197541 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001462985197541/10000000000000000 : ℝ)) (X := (100060404819534564349/100000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054165338855779477/50000000000000000000 : ℝ) ≤ (10002623679117227/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (50054165338855779477/50000000000000000000 : ℝ)^1024 ≤ (10002623679117227/10000000000000000 : ℝ)^4227 := by
      have hnat : (50054165338855779477 : ℕ)^1024*10000000000000000^4227 ≤ 10002623679117227^4227*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054165338855779477 50000000000000000000 10002623679117227 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002623679117227/10000000000000000 : ℝ)) (X := (50054165338855779477/50000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(779935084848109/12500000000000000000 : ℝ) ≤ ((13177950701262231709/13182000000000000000 : ℝ)+2*(580346959843/329550000000000 : ℝ)*(479/5000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (13177950701262231709/13182000000000000000 : ℝ)+2*(580346959843/329550000000000 : ℝ)*(479/5000 : ℝ)=(2000060458255571/2000000000000000 : ℝ) by norm_num, show 1+2*(779935084848109/12500000000000000000 : ℝ)=(6250779935084848109/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54165338855779477/100000000000000000000 : ℝ)+(779935084848109/12500000000000000000 : ℝ) ≤ ((13177950701262231709/13182000000000000000 : ℝ)+(580346959843/329550000000000 : ℝ)*((16171/100000 : ℝ)+(479/5000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (13177950701262231709/13182000000000000000 : ℝ)+(580346959843/329550000000000 : ℝ)*((16171/100000 : ℝ)+(479/5000 : ℝ))=(10001462985197541/10000000000000000 : ℝ) by norm_num, show 1+(54165338855779477/100000000000000000000 : ℝ)+(779935084848109/12500000000000000000 : ℝ)=(100060404819534564349/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54165338855779477/100000000000000000000 : ℝ) ≤ ((13177950701262231709/13182000000000000000 : ℝ)+2*(580346959843/329550000000000 : ℝ)*(16171/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (13177950701262231709/13182000000000000000 : ℝ)+2*(580346959843/329550000000000 : ℝ)*(16171/100000 : ℝ)=(10002623679117227/10000000000000000 : ℝ) by norm_num, show 1+2*(54165338855779477/100000000000000000000 : ℝ)=(50054165338855779477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13177950701262231709/13182000000000000000 : ℝ)*(X 1 0+X 2 0)+(580346959843/329550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (479/5000 : ℝ)) (hi := (16171/100000 : ℝ)) (c := (13177950701262231709/13182000000000000000 : ℝ)) (alpha := (580346959843/329550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13177950701262231709/13182000000000000000 : ℝ)*(X 0 1+X 2 1)+(580346959843/329550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (479/5000 : ℝ)) (hi := (16171/100000 : ℝ)) (c := (13177950701262231709/13182000000000000000 : ℝ)) (alpha := (580346959843/329550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13177950701262231709/13182000000000000000 : ℝ)*(X 0 2+X 1 2)+(580346959843/329550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (479/5000 : ℝ)) (hi := (16171/100000 : ℝ)) (c := (13177950701262231709/13182000000000000000 : ℝ)) (alpha := (580346959843/329550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054052621/5000000000 : ℝ)*X 0 0+(1354481611/2500000000 : ℝ)*X 0 1+(655266723/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675525293/5000000000 : ℝ)*X 1 0+(-439550313/2000000000 : ℝ)*X 1 1+(524213389/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070210113/2000000000 : ℝ)*X 2 0+(5242134367/10000000000 : ℝ)*X 2 1+(-2197750961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346433579/10000000000 : ℝ)*X 0 0+(4171005173/10000000000 : ℝ)*X 0 1+(1132247207/2500000000 : ℝ)*X 0 2+(4346433579/10000000000 : ℝ)*X 1 0+(4171005173/10000000000 : ℝ)*X 1 1+(1132247207/2500000000 : ℝ)*X 1 2+(4346433579/10000000000 : ℝ)*X 2 0+(4171005173/10000000000 : ℝ)*X 2 1+(1132247207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108119223/10000000000 : ℝ)*X 0 0+(2621382411/5000000000 : ℝ)*X 0 1+(5417291661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2653071341/5000000000 : ℝ)*X 1 0+(-12641207/62500000 : ℝ)*X 1 1+(10834583/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265307101/500000000 : ℝ)*X 2 0+(1083458389/2000000000 : ℝ)*X 2 1+(-2022593411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346461433/10000000000 : ℝ)*X 0 0+(2263851503/5000000000 : ℝ)*X 0 1+(208614847/500000000 : ℝ)*X 0 2+(4346461433/10000000000 : ℝ)*X 1 0+(2263851503/5000000000 : ℝ)*X 1 1+(208614847/500000000 : ℝ)*X 1 2+(4346461433/10000000000 : ℝ)*X 2 0+(2263851503/5000000000 : ℝ)*X 2 1+(208614847/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (265936408894261642075776729/54925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374667803/100000000000000 : ℝ)*(base19) + (230723359/100000000000000 : ℝ)*(lower2) + (85101377/100000000000000 : ℝ)*(lower3) + (3838239/100000000000000 : ℝ)*(lower4) + (1060249719427927/25000000000000 : ℝ)*(major0) + (1060249719427927/25000000000000 : ℝ)*(major1) + (1060249719427927/25000000000000 : ℝ)*(major2) + (2844269207215601/50000000000000 : ℝ)*(sp0) + (5688556518056969/100000000000000 : ℝ)*(sp1) + (2844282715596537/50000000000000 : ℝ)*(sp2) + (1396713753437643/50000000000000 : ℝ)*(sp3) + (27016761871/100000000000000 : ℝ)*(sp4) + (8538468301/100000000000000 : ℝ)*(sp5) + (2327980693/50000000000000 : ℝ)*(sp7) + (43647377544323/1562500000000 : ℝ)*(f.failure) + (2844282715596537/50000000000000 : ℝ)*(f.sum) + (247486263768637/32955000000000000000000000000 : ℝ)*base66 + (43672649502222757/329550000000000000000000000000000 : ℝ)*base68 + (1597191551905872757/329550000000000000000000000000000 : ℝ)*base70 + (1748969792290422757/329550000000000000000000000000000 : ℝ)*base72 + (33135000019807/32955000000000000000000000000 : ℝ)*base74 + (289977038870922757/329550000000000000000000000000000 : ℝ)*base76 + (5987915317948122757/329550000000000000000000000000000 : ℝ)*base78 + (1646460992213622757/329550000000000000000000000000000 : ℝ)*base80 + (23567707929641/16477500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (60893/39062500000000000000 : ℝ)*base89 + (60893/39062500000000000000 : ℝ)*base91 + (60893/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131167138586263937667673497/27462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1398451561/50000000000000 : ℝ)*(base19) + (2011437277/100000000000000 : ℝ)*(base23) + (20717067/50000000000000 : ℝ)*(upper3) + (61972541/100000000000000 : ℝ)*(lower4) + (446084221/100000000000000 : ℝ)*(upper5) + (533966140127689/12500000000000 : ℝ)*(major0) + (533966140127689/12500000000000 : ℝ)*(major1) + (533966140127689/12500000000000 : ℝ)*(major2) + (2621765627/4000000000000 : ℝ)*(sp1) + (43400356983/100000000000000 : ℝ)*(sp2) + (1145956946661869/20000000000000 : ℝ)*(sp4) + (5729716392265549/100000000000000 : ℝ)*(sp5) + (1145947864303017/20000000000000 : ℝ)*(sp6) + (175854584345381/6250000000000 : ℝ)*(sp7) + (175854584345381/6250000000000 : ℝ)*(f.failure) + (1145956946661869/20000000000000 : ℝ)*(f.sum) + (61162153144717/32955000000000000000000000000 : ℝ)*base65 + (546317253575120501/164775000000000000000000000000000 : ℝ)*base67 + (1561559941666895501/164775000000000000000000000000000 : ℝ)*base69 + (1190554981933370501/164775000000000000000000000000000 : ℝ)*base71 + (16284077381677/32955000000000000000000000000 : ℝ)*base73 + (888678621213020501/164775000000000000000000000000000 : ℝ)*base75 + (1913263219031945501/164775000000000000000000000000000 : ℝ)*base77 + (2159569383521720501/164775000000000000000000000000000 : ℝ)*base79 + (101261081989061/16477500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1215329/156250000000000000000 : ℝ)*base90 + (1215329/156250000000000000000 : ℝ)*base92 + (1215329/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1262_s4_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110274313/10000000000 : ℝ)*x 0 + (5396697609/10000000000 : ℝ)*x 1 + (5261940847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110274313/10000000000 : ℝ)^8455 ≤ (1283404588363/10000000000000 : ℝ)^6407 := by
    have hnat : (2110274313 : ℕ)^8455*10000000000000^6407 ≤ 1283404588363^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110274313 10000000000 1283404588363 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396697609/10000000000 : ℝ)^8455 ≤ (44310099345907/100000000000000 : ℝ)^6407 := by
    have hnat : (5396697609 : ℕ)^8455*100000000000000^6407 ≤ 44310099345907^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396697609 10000000000 44310099345907 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261940847/10000000000 : ℝ)^8455 ≤ (21427927382053/50000000000000 : ℝ)^6407 := by
    have hnat : (5261940847 : ℕ)^8455*50000000000000^6407 ≤ 21427927382053^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261940847 10000000000 21427927382053 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110274313/10000000000 : ℝ), (5396697609/10000000000 : ℝ), (5261940847/10000000000 : ℝ)] ![(1283404588363/10000000000000 : ℝ), (44310099345907/100000000000000 : ℝ), (21427927382053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110274313/10000000000 : ℝ)|^8455 ≤ (1283404588363/10000000000000 : ℝ)^6407
        have hw : |(-2110274313/10000000000 : ℝ)|=(2110274313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396697609/10000000000 : ℝ)|^8455 ≤ (44310099345907/100000000000000 : ℝ)^6407
        have hw : |(5396697609/10000000000 : ℝ)|=(5396697609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261940847/10000000000 : ℝ)|^8455 ≤ (21427927382053/50000000000000 : ℝ)^6407
        have hw : |(5261940847/10000000000 : ℝ)|=(5261940847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672844523/5000000000 : ℝ)*x 0 + (-2178682303/10000000000 : ℝ)*x 1 + (657742609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672844523/5000000000 : ℝ)^8455 ≤ (43758252398049/100000000000000 : ℝ)^6407 := by
    have hnat : (2672844523 : ℕ)^8455*100000000000000^6407 ≤ 43758252398049^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672844523 5000000000 43758252398049 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178682303/10000000000 : ℝ)^8455 ≤ (3346473138097/25000000000000 : ℝ)^6407 := by
    have hnat : (2178682303 : ℕ)^8455*25000000000000^6407 ≤ 3346473138097^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178682303 10000000000 3346473138097 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657742609/1250000000 : ℝ)^8455 ≤ (42855855032803/100000000000000 : ℝ)^6407 := by
    have hnat : (657742609 : ℕ)^8455*100000000000000^6407 ≤ 42855855032803^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657742609 1250000000 42855855032803 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672844523/5000000000 : ℝ), (-2178682303/10000000000 : ℝ), (657742609/1250000000 : ℝ)] ![(43758252398049/100000000000000 : ℝ), (3346473138097/25000000000000 : ℝ), (42855855032803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672844523/5000000000 : ℝ)|^8455 ≤ (43758252398049/100000000000000 : ℝ)^6407
        have hw : |(2672844523/5000000000 : ℝ)|=(2672844523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178682303/10000000000 : ℝ)|^8455 ≤ (3346473138097/25000000000000 : ℝ)^6407
        have hw : |(-2178682303/10000000000 : ℝ)|=(2178682303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657742609/1250000000 : ℝ)|^8455 ≤ (42855855032803/100000000000000 : ℝ)^6407
        have hw : |(657742609/1250000000 : ℝ)|=(657742609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167052811/312500000 : ℝ)*x 0 + (2630970321/5000000000 : ℝ)*x 1 + (-10893407/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167052811/312500000 : ℝ)^8455 ≤ (43758262184909/100000000000000 : ℝ)^6407 := by
    have hnat : (167052811 : ℕ)^8455*100000000000000^6407 ≤ 43758262184909^6407*312500000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167052811 312500000 43758262184909 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630970321/5000000000 : ℝ)^8455 ≤ (42855852560789/100000000000000 : ℝ)^6407 := by
    have hnat : (2630970321 : ℕ)^8455*100000000000000^6407 ≤ 42855852560789^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630970321 5000000000 42855852560789 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10893407/50000000 : ℝ)^8455 ≤ (1673235653861/12500000000000 : ℝ)^6407 := by
    have hnat : (10893407 : ℕ)^8455*12500000000000^6407 ≤ 1673235653861^6407*50000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10893407 50000000 1673235653861 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167052811/312500000 : ℝ), (2630970321/5000000000 : ℝ), (-10893407/50000000 : ℝ)] ![(43758262184909/100000000000000 : ℝ), (42855852560789/100000000000000 : ℝ), (1673235653861/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167052811/312500000 : ℝ)|^8455 ≤ (43758262184909/100000000000000 : ℝ)^6407
        have hw : |(167052811/312500000 : ℝ)|=(167052811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630970321/5000000000 : ℝ)|^8455 ≤ (42855852560789/100000000000000 : ℝ)^6407
        have hw : |(2630970321/5000000000 : ℝ)|=(2630970321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10893407/50000000 : ℝ)|^8455 ≤ (1673235653861/12500000000000 : ℝ)^6407
        have hw : |(-10893407/50000000 : ℝ)|=(10893407/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347736283/10000000000 : ℝ)*x 0 + (4212621577/10000000000 : ℝ)*x 1 + (4487041033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347736283/10000000000 : ℝ)^8455 ≤ (33314544915253/100000000000000 : ℝ)^6407 := by
    have hnat : (4347736283 : ℕ)^8455*100000000000000^6407 ≤ 33314544915253^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347736283 10000000000 33314544915253 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212621577/10000000000 : ℝ)^8455 ≤ (639102461057/2000000000000 : ℝ)^6407 := by
    have hnat : (4212621577 : ℕ)^8455*2000000000000^6407 ≤ 639102461057^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212621577 10000000000 639102461057 2000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487041033/10000000000 : ℝ)^8455 ≤ (34730332016761/100000000000000 : ℝ)^6407 := by
    have hnat : (4487041033 : ℕ)^8455*100000000000000^6407 ≤ 34730332016761^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487041033 10000000000 34730332016761 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347736283/10000000000 : ℝ), (4212621577/10000000000 : ℝ), (4487041033/10000000000 : ℝ)] ![(33314544915253/100000000000000 : ℝ), (639102461057/2000000000000 : ℝ), (34730332016761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347736283/10000000000 : ℝ)|^8455 ≤ (33314544915253/100000000000000 : ℝ)^6407
        have hw : |(4347736283/10000000000 : ℝ)|=(4347736283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212621577/10000000000 : ℝ)|^8455 ≤ (639102461057/2000000000000 : ℝ)^6407
        have hw : |(4212621577/10000000000 : ℝ)|=(4212621577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487041033/10000000000 : ℝ)|^8455 ≤ (34730332016761/100000000000000 : ℝ)^6407
        have hw : |(4487041033/10000000000 : ℝ)|=(4487041033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055140049/5000000000 : ℝ)*x 0 + (5262312149/10000000000 : ℝ)*x 1 + (2698162501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055140049/5000000000 : ℝ)^8455 ≤ (6417046156197/50000000000000 : ℝ)^6407 := by
    have hnat : (1055140049 : ℕ)^8455*50000000000000^6407 ≤ 6417046156197^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055140049 5000000000 6417046156197 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262312149/10000000000 : ℝ)^8455 ≤ (5357480690127/12500000000000 : ℝ)^6407 := by
    have hnat : (5262312149 : ℕ)^8455*12500000000000^6407 ≤ 5357480690127^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262312149 10000000000 5357480690127 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698162501/5000000000 : ℝ)^8455 ≤ (2215303107537/5000000000000 : ℝ)^6407 := by
    have hnat : (2698162501 : ℕ)^8455*5000000000000^6407 ≤ 2215303107537^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698162501 5000000000 2215303107537 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055140049/5000000000 : ℝ), (5262312149/10000000000 : ℝ), (2698162501/5000000000 : ℝ)] ![(6417046156197/50000000000000 : ℝ), (5357480690127/12500000000000 : ℝ), (2215303107537/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055140049/5000000000 : ℝ)|^8455 ≤ (6417046156197/50000000000000 : ℝ)^6407
        have hw : |(-1055140049/5000000000 : ℝ)|=(1055140049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262312149/10000000000 : ℝ)|^8455 ≤ (5357480690127/12500000000000 : ℝ)^6407
        have hw : |(5262312149/10000000000 : ℝ)|=(5262312149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698162501/5000000000 : ℝ)|^8455 ≤ (2215303107537/5000000000000 : ℝ)^6407
        have hw : |(2698162501/5000000000 : ℝ)|=(2698162501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327815399/2500000000 : ℝ)*x 0 + (-1022148583/5000000000 : ℝ)*x 1 + (2698162481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327815399/2500000000 : ℝ)^8455 ≤ (1084668525673/2500000000000 : ℝ)^6407 := by
    have hnat : (1327815399 : ℕ)^8455*2500000000000^6407 ≤ 1084668525673^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327815399 2500000000 1084668525673 2500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022148583/5000000000 : ℝ)^8455 ≤ (492287889827/4000000000000 : ℝ)^6407 := by
    have hnat : (1022148583 : ℕ)^8455*4000000000000^6407 ≤ 492287889827^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022148583 5000000000 492287889827 4000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698162481/5000000000 : ℝ)^8455 ≤ (8861212343469/20000000000000 : ℝ)^6407 := by
    have hnat : (2698162481 : ℕ)^8455*20000000000000^6407 ≤ 8861212343469^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698162481 5000000000 8861212343469 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327815399/2500000000 : ℝ), (-1022148583/5000000000 : ℝ), (2698162481/5000000000 : ℝ)] ![(1084668525673/2500000000000 : ℝ), (492287889827/4000000000000 : ℝ), (8861212343469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327815399/2500000000 : ℝ)|^8455 ≤ (1084668525673/2500000000000 : ℝ)^6407
        have hw : |(1327815399/2500000000 : ℝ)|=(1327815399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022148583/5000000000 : ℝ)|^8455 ≤ (492287889827/4000000000000 : ℝ)^6407
        have hw : |(-1022148583/5000000000 : ℝ)|=(1022148583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698162481/5000000000 : ℝ)|^8455 ≤ (8861212343469/20000000000000 : ℝ)^6407
        have hw : |(2698162481/5000000000 : ℝ)|=(2698162481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655630699/5000000000 : ℝ)*x 0 + (1079265021/2000000000 : ℝ)*x 1 + (-2044297239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655630699/5000000000 : ℝ)^8455 ≤ (43386738892483/100000000000000 : ℝ)^6407 := by
    have hnat : (2655630699 : ℕ)^8455*100000000000000^6407 ≤ 43386738892483^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655630699 5000000000 43386738892483 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079265021/2000000000 : ℝ)^8455 ≤ (11076515816683/25000000000000 : ℝ)^6407 := by
    have hnat : (1079265021 : ℕ)^8455*25000000000000^6407 ≤ 11076515816683^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079265021 2000000000 11076515816683 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044297239/10000000000 : ℝ)^8455 ≤ (6153598912817/50000000000000 : ℝ)^6407 := by
    have hnat : (2044297239 : ℕ)^8455*50000000000000^6407 ≤ 6153598912817^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044297239 10000000000 6153598912817 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655630699/5000000000 : ℝ), (1079265021/2000000000 : ℝ), (-2044297239/10000000000 : ℝ)] ![(43386738892483/100000000000000 : ℝ), (11076515816683/25000000000000 : ℝ), (6153598912817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655630699/5000000000 : ℝ)|^8455 ≤ (43386738892483/100000000000000 : ℝ)^6407
        have hw : |(2655630699/5000000000 : ℝ)|=(2655630699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079265021/2000000000 : ℝ)|^8455 ≤ (11076515816683/25000000000000 : ℝ)^6407
        have hw : |(1079265021/2000000000 : ℝ)|=(1079265021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044297239/10000000000 : ℝ)|^8455 ≤ (6153598912817/50000000000000 : ℝ)^6407
        have hw : |(-2044297239/10000000000 : ℝ)|=(2044297239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s4_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347748491/10000000000 : ℝ)*x 0 + (2243142629/5000000000 : ℝ)*x 1 + (4213380379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347748491/10000000000 : ℝ)^8455 ≤ (33314668360477/100000000000000 : ℝ)^6407 := by
    have hnat : (4347748491 : ℕ)^8455*100000000000000^6407 ≤ 33314668360477^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347748491 10000000000 33314668360477 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243142629/5000000000 : ℝ)^8455 ≤ (17361306263353/50000000000000 : ℝ)^6407 := by
    have hnat : (2243142629 : ℕ)^8455*50000000000000^6407 ≤ 17361306263353^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243142629 5000000000 17361306263353 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4213380379/10000000000 : ℝ)^8455 ≤ (31962719104399/100000000000000 : ℝ)^6407 := by
    have hnat : (4213380379 : ℕ)^8455*100000000000000^6407 ≤ 31962719104399^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213380379 10000000000 31962719104399 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347748491/10000000000 : ℝ), (2243142629/5000000000 : ℝ), (4213380379/10000000000 : ℝ)] ![(33314668360477/100000000000000 : ℝ), (17361306263353/50000000000000 : ℝ), (31962719104399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347748491/10000000000 : ℝ)|^8455 ≤ (33314668360477/100000000000000 : ℝ)^6407
        have hw : |(4347748491/10000000000 : ℝ)|=(4347748491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243142629/5000000000 : ℝ)|^8455 ≤ (17361306263353/50000000000000 : ℝ)^6407
        have hw : |(2243142629/5000000000 : ℝ)|=(2243142629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4213380379/10000000000 : ℝ)|^8455 ≤ (31962719104399/100000000000000 : ℝ)^6407
        have hw : |(4213380379/10000000000 : ℝ)|=(4213380379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1423/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5481/50000 : ℝ) ^ (4227/1024 : ℝ) ≤ (2176519630303787/20000000000000000000 : ℝ) := by
    have hpowers : (5481/50000 : ℝ)^4227 ≤ (2176519630303787/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5481 : ℕ)^4227*20000000000000000000^1024 ≤ 2176519630303787^1024*50000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5481 50000 2176519630303787 20000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5481/50000 : ℝ)) (X := (2176519630303787/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14683/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (1454554720423907/4000000000000000000 : ℝ) := by
    have hpowers : (14683/100000 : ℝ)^4227 ≤ (1454554720423907/4000000000000000000 : ℝ)^1024 := by
      have hnat : (14683 : ℕ)^4227*4000000000000000000^1024 ≤ 1454554720423907^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14683 100000 1454554720423907 4000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14683/100000 : ℝ)) (X := (1454554720423907/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002176519630303787/10000000000000000000 : ℝ) ≤ (156258237862017/156250000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (10002176519630303787/10000000000000000000 : ℝ)^1024 ≤ (156258237862017/156250000000000 : ℝ)^4227 := by
      have hnat : (10002176519630303787 : ℕ)^1024*156250000000000^4227 ≤ 156258237862017^4227*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002176519630303787 10000000000000000000 156258237862017 156250000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156258237862017/156250000000000 : ℝ)) (X := (10002176519630303787/10000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004724646616211661/10000000000000000000 : ℝ) ≤ (5000572175578887/5000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (10004724646616211661/10000000000000000000 : ℝ)^1024 ≤ (5000572175578887/5000000000000000 : ℝ)^4227 := by
      have hnat : (10004724646616211661 : ℕ)^1024*5000000000000000^4227 ≤ 5000572175578887^4227*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004724646616211661 10000000000000000000 5000572175578887 5000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000572175578887/5000000000000000 : ℝ)) (X := (10004724646616211661/10000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001454554720423907/2000000000000000000 : ℝ) ≤ (500088073957323/500000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (2001454554720423907/2000000000000000000 : ℝ)^1024 ≤ (500088073957323/500000000000000 : ℝ)^4227 := by
      have hnat : (2001454554720423907 : ℕ)^1024*500000000000000^4227 ≤ 500088073957323^4227*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001454554720423907 2000000000000000000 500088073957323 500000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500088073957323/500000000000000 : ℝ)) (X := (2001454554720423907/2000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2176519630303787/20000000000000000000 : ℝ) ≤ ((4649803985423528073/4651250000000000000 : ℝ)+2*(308563994343/186050000000000 : ℝ)*(5481/50000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (4649803985423528073/4651250000000000000 : ℝ)+2*(308563994343/186050000000000 : ℝ)*(5481/50000 : ℝ)=(156258237862017/156250000000000 : ℝ) by norm_num, show 1+2*(2176519630303787/20000000000000000000 : ℝ)=(10002176519630303787/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1454554720423907/4000000000000000000 : ℝ)+(2176519630303787/20000000000000000000 : ℝ) ≤ ((4649803985423528073/4651250000000000000 : ℝ)+(308563994343/186050000000000 : ℝ)*((14683/100000 : ℝ)+(5481/50000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (4649803985423528073/4651250000000000000 : ℝ)+(308563994343/186050000000000 : ℝ)*((14683/100000 : ℝ)+(5481/50000 : ℝ))=(5000572175578887/5000000000000000 : ℝ) by norm_num, show 1+(1454554720423907/4000000000000000000 : ℝ)+(2176519630303787/20000000000000000000 : ℝ)=(10004724646616211661/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1454554720423907/4000000000000000000 : ℝ) ≤ ((4649803985423528073/4651250000000000000 : ℝ)+2*(308563994343/186050000000000 : ℝ)*(14683/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (4649803985423528073/4651250000000000000 : ℝ)+2*(308563994343/186050000000000 : ℝ)*(14683/100000 : ℝ)=(500088073957323/500000000000000 : ℝ) by norm_num, show 1+2*(1454554720423907/4000000000000000000 : ℝ)=(2001454554720423907/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4649803985423528073/4651250000000000000 : ℝ)*(X 1 0+X 2 0)+(308563994343/186050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (4649803985423528073/4651250000000000000 : ℝ)) (alpha := (308563994343/186050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4649803985423528073/4651250000000000000 : ℝ)*(X 0 1+X 2 1)+(308563994343/186050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (4649803985423528073/4651250000000000000 : ℝ)) (alpha := (308563994343/186050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4649803985423528073/4651250000000000000 : ℝ)*(X 0 2+X 1 2)+(308563994343/186050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (4649803985423528073/4651250000000000000 : ℝ)) (alpha := (308563994343/186050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2110274313/10000000000 : ℝ)*X 0 0+(5396697609/10000000000 : ℝ)*X 0 1+(5261940847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672844523/5000000000 : ℝ)*X 1 0+(-2178682303/10000000000 : ℝ)*X 1 1+(657742609/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167052811/312500000 : ℝ)*X 2 0+(2630970321/5000000000 : ℝ)*X 2 1+(-10893407/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347736283/10000000000 : ℝ)*X 0 0+(4212621577/10000000000 : ℝ)*X 0 1+(4487041033/10000000000 : ℝ)*X 0 2+(4347736283/10000000000 : ℝ)*X 1 0+(4212621577/10000000000 : ℝ)*X 1 1+(4487041033/10000000000 : ℝ)*X 1 2+(4347736283/10000000000 : ℝ)*X 2 0+(4212621577/10000000000 : ℝ)*X 2 1+(4487041033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1055140049/5000000000 : ℝ)*X 0 0+(5262312149/10000000000 : ℝ)*X 0 1+(2698162501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327815399/2500000000 : ℝ)*X 1 0+(-1022148583/5000000000 : ℝ)*X 1 1+(2698162481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655630699/5000000000 : ℝ)*X 2 0+(1079265021/2000000000 : ℝ)*X 2 1+(-2044297239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347748491/10000000000 : ℝ)*X 0 0+(2243142629/5000000000 : ℝ)*X 0 1+(4213380379/10000000000 : ℝ)*X 0 2+(4347748491/10000000000 : ℝ)*X 1 0+(2243142629/5000000000 : ℝ)*X 1 1+(4213380379/10000000000 : ℝ)*X 1 2+(4347748491/10000000000 : ℝ)*X 2 0+(2243142629/5000000000 : ℝ)*X 2 1+(4213380379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2231531655297871237988483673/232562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20145543/12500000000000 : ℝ)*(base19) + (353886509/25000000000000 : ℝ)*(base23) + (120860707/100000000000000 : ℝ)*(upper4) + (106682029/20000000000000 : ℝ)*(upper5) + (5532446280870311/100000000000000 : ℝ)*(major0) + (5532446280870311/100000000000000 : ℝ)*(major1) + (5532446280870311/100000000000000 : ℝ)*(major2) + (1855194168485983/25000000000000 : ℝ)*(sp0) + (231899486735931/3125000000000 : ℝ)*(sp1) + (927602114026463/12500000000000 : ℝ)*(sp2) + (182203309060893/5000000000000 : ℝ)*(sp3) + (2603363363/6250000000000 : ℝ)*(sp4) + (34591043603/100000000000000 : ℝ)*(sp5) + (7732918131/100000000000000 : ℝ)*(sp7) + (455509239266999/12500000000000 : ℝ)*(f.failure) + (371040916387887/5000000000000 : ℝ)*(f.sum) + (58930567238741/18605000000000000000000000000 : ℝ)*base65 + (2175352173027815703/465125000000000000000000000000000 : ℝ)*base67 + (8498899085681440703/465125000000000000000000000000000 : ℝ)*base69 + (10183891389392440703/465125000000000000000000000000000 : ℝ)*base71 + (6494386476613/9302500000000000000000000000 : ℝ)*base73 + (13264849519995190703/465125000000000000000000000000000 : ℝ)*base75 + (4847861392798940703/465125000000000000000000000000000 : ℝ)*base77 + (12901663990859315703/465125000000000000000000000000000 : ℝ)*base79 + (101266195844801/18605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1533091/312500000000000000000 : ℝ)*base90 + (1533091/312500000000000000000 : ℝ)*base92 + (1533091/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34459327145897283561217557/11628125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (317943699/100000000000000 : ℝ)*(base19) + (18982167/50000000000000 : ℝ)*(base23) + (149197/1250000000000 : ℝ)*(upper2) + (6071711/10000000000000 : ℝ)*(upper3) + (985101/5000000000000 : ℝ)*(upper5) + (556312271284603/10000000000000 : ℝ)*(major0) + (556312271284603/10000000000000 : ℝ)*(major1) + (556312271284603/10000000000000 : ℝ)*(major2) + (2076360901/50000000000000 : ℝ)*(sp1) + (12739763/3125000000000 : ℝ)*(sp2) + (3730982835083467/50000000000000 : ℝ)*(sp4) + (3730980599750717/50000000000000 : ℝ)*(sp5) + (932745653066273/12500000000000 : ℝ)*(sp6) + (916069914185891/25000000000000 : ℝ)*(sp7) + (916069914185891/25000000000000 : ℝ)*(f.failure) + (3730982835083467/50000000000000 : ℝ)*(f.sum) + (890650894329/930250000000000000000000000 : ℝ)*base66 + (136199831121589981/46512500000000000000000000000000 : ℝ)*base68 + (3377020965085019/46512500000000000000000000000000 : ℝ)*base69 + (650535558549614981/46512500000000000000000000000000 : ℝ)*base72 + (7849220975607/1860500000000000000000000000 : ℝ)*base73 + (405021472828214981/46512500000000000000000000000000 : ℝ)*base76 + (561970721617964981/46512500000000000000000000000000 : ℝ)*base78 + (344386024120914981/46512500000000000000000000000000 : ℝ)*base80 + (3210824970417/465125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3678919/625000000000000000000 : ℝ)*base90 + (3678919/625000000000000000000 : ℝ)*base92 + (3678919/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1262_s5_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527673917/2500000000 : ℝ)*x 0 + (2695964551/5000000000 : ℝ)*x 1 + (1316608029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527673917/2500000000 : ℝ)^8455 ≤ (6418713832679/50000000000000 : ℝ)^6407 := by
    have hnat : (527673917 : ℕ)^8455*50000000000000^6407 ≤ 6418713832679^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527673917 2500000000 6418713832679 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695964551/5000000000 : ℝ)^8455 ≤ (11064609830467/25000000000000 : ℝ)^6407 := by
    have hnat : (2695964551 : ℕ)^8455*25000000000000^6407 ≤ 11064609830467^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695964551 5000000000 11064609830467 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316608029/2500000000 : ℝ)^8455 ≤ (21452066499589/50000000000000 : ℝ)^6407 := by
    have hnat : (1316608029 : ℕ)^8455*50000000000000^6407 ≤ 21452066499589^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316608029 2500000000 21452066499589 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527673917/2500000000 : ℝ), (2695964551/5000000000 : ℝ), (1316608029/2500000000 : ℝ)] ![(6418713832679/50000000000000 : ℝ), (11064609830467/25000000000000 : ℝ), (21452066499589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527673917/2500000000 : ℝ)|^8455 ≤ (6418713832679/50000000000000 : ℝ)^6407
        have hw : |(-527673917/2500000000 : ℝ)|=(527673917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695964551/5000000000 : ℝ)|^8455 ≤ (11064609830467/25000000000000 : ℝ)^6407
        have hw : |(2695964551/5000000000 : ℝ)|=(2695964551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316608029/2500000000 : ℝ)|^8455 ≤ (21452066499589/50000000000000 : ℝ)^6407
        have hw : |(1316608029/2500000000 : ℝ)|=(1316608029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344480529/10000000000 : ℝ)*x 0 + (-2174336551/10000000000 : ℝ)*x 1 + (329152009/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344480529/10000000000 : ℝ)^8455 ≤ (5468149767343/12500000000000 : ℝ)^6407 := by
    have hnat : (5344480529 : ℕ)^8455*12500000000000^6407 ≤ 5468149767343^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344480529 10000000000 5468149767343 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174336551/10000000000 : ℝ)^8455 ≤ (2670133709733/20000000000000 : ℝ)^6407 := by
    have hnat : (2174336551 : ℕ)^8455*20000000000000^6407 ≤ 2670133709733^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174336551 10000000000 2670133709733 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329152009/625000000 : ℝ)^8455 ≤ (42904133300201/100000000000000 : ℝ)^6407 := by
    have hnat : (329152009 : ℕ)^8455*100000000000000^6407 ≤ 42904133300201^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329152009 625000000 42904133300201 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344480529/10000000000 : ℝ), (-2174336551/10000000000 : ℝ), (329152009/625000000 : ℝ)] ![(5468149767343/12500000000000 : ℝ), (2670133709733/20000000000000 : ℝ), (42904133300201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344480529/10000000000 : ℝ)|^8455 ≤ (5468149767343/12500000000000 : ℝ)^6407
        have hw : |(5344480529/10000000000 : ℝ)|=(5344480529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2174336551/10000000000 : ℝ)|^8455 ≤ (2670133709733/20000000000000 : ℝ)^6407
        have hw : |(-2174336551/10000000000 : ℝ)|=(2174336551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329152009/625000000 : ℝ)|^8455 ≤ (42904133300201/100000000000000 : ℝ)^6407
        have hw : |(329152009/625000000 : ℝ)|=(329152009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668060087/1250000000 : ℝ)*x 0 + (2633216057/5000000000 : ℝ)*x 1 + (-135896023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668060087/1250000000 : ℝ)^8455 ≤ (43745199942593/100000000000000 : ℝ)^6407 := by
    have hnat : (668060087 : ℕ)^8455*100000000000000^6407 ≤ 43745199942593^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668060087 1250000000 43745199942593 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633216057/5000000000 : ℝ)^8455 ≤ (10726033244419/25000000000000 : ℝ)^6407 := by
    have hnat : (2633216057 : ℕ)^8455*25000000000000^6407 ≤ 10726033244419^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633216057 5000000000 10726033244419 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135896023/625000000 : ℝ)^8455 ≤ (13350667065853/100000000000000 : ℝ)^6407 := by
    have hnat : (135896023 : ℕ)^8455*100000000000000^6407 ≤ 13350667065853^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135896023 625000000 13350667065853 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668060087/1250000000 : ℝ), (2633216057/5000000000 : ℝ), (-135896023/625000000 : ℝ)] ![(43745199942593/100000000000000 : ℝ), (10726033244419/25000000000000 : ℝ), (13350667065853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668060087/1250000000 : ℝ)|^8455 ≤ (43745199942593/100000000000000 : ℝ)^6407
        have hw : |(668060087/1250000000 : ℝ)|=(668060087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633216057/5000000000 : ℝ)|^8455 ≤ (10726033244419/25000000000000 : ℝ)^6407
        have hw : |(2633216057/5000000000 : ℝ)|=(2633216057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135896023/625000000 : ℝ)|^8455 ≤ (13350667065853/100000000000000 : ℝ)^6407
        have hw : |(-135896023/625000000 : ℝ)|=(135896023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (173919311/400000000 : ℝ)*x 0 + (4222018591/10000000000 : ℝ)*x 1 + (4477581189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173919311/400000000 : ℝ)^8455 ≤ (33317037422003/100000000000000 : ℝ)^6407 := by
    have hnat : (173919311 : ℕ)^8455*100000000000000^6407 ≤ 33317037422003^6407*400000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173919311 400000000 33317037422003 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222018591/10000000000 : ℝ)^8455 ≤ (3204922346739/10000000000000 : ℝ)^6407 := by
    have hnat : (4222018591 : ℕ)^8455*10000000000000^6407 ≤ 3204922346739^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222018591 10000000000 3204922346739 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477581189/10000000000 : ℝ)^8455 ≤ (34633739090057/100000000000000 : ℝ)^6407 := by
    have hnat : (4477581189 : ℕ)^8455*100000000000000^6407 ≤ 34633739090057^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477581189 10000000000 34633739090057 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173919311/400000000 : ℝ), (4222018591/10000000000 : ℝ), (4477581189/10000000000 : ℝ)] ![(33317037422003/100000000000000 : ℝ), (3204922346739/10000000000000 : ℝ), (34633739090057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173919311/400000000 : ℝ)|^8455 ≤ (33317037422003/100000000000000 : ℝ)^6407
        have hw : |(173919311/400000000 : ℝ)|=(173919311/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222018591/10000000000 : ℝ)|^8455 ≤ (3204922346739/10000000000000 : ℝ)^6407
        have hw : |(4222018591/10000000000 : ℝ)|=(4222018591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477581189/10000000000 : ℝ)|^8455 ≤ (34633739090057/100000000000000 : ℝ)^6407
        have hw : |(4477581189/10000000000 : ℝ)|=(4477581189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42214011/200000000 : ℝ)*x 0 + (2633377189/5000000000 : ℝ)*x 1 + (5391605633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42214011/200000000 : ℝ)^8455 ≤ (6418733424699/50000000000000 : ℝ)^6407 := by
    have hnat : (42214011 : ℕ)^8455*50000000000000^6407 ≤ 6418733424699^6407*200000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42214011 200000000 6418733424699 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633377189/5000000000 : ℝ)^8455 ≤ (21453798806657/50000000000000 : ℝ)^6407 := by
    have hnat : (2633377189 : ℕ)^8455*50000000000000^6407 ≤ 21453798806657^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633377189 5000000000 21453798806657 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391605633/10000000000 : ℝ)^8455 ≤ (22127467760919/50000000000000 : ℝ)^6407 := by
    have hnat : (5391605633 : ℕ)^8455*50000000000000^6407 ≤ 22127467760919^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391605633 10000000000 22127467760919 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42214011/200000000 : ℝ), (2633377189/5000000000 : ℝ), (5391605633/10000000000 : ℝ)] ![(6418733424699/50000000000000 : ℝ), (21453798806657/50000000000000 : ℝ), (22127467760919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42214011/200000000 : ℝ)|^8455 ≤ (6418733424699/50000000000000 : ℝ)^6407
        have hw : |(-42214011/200000000 : ℝ)|=(42214011/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633377189/5000000000 : ℝ)|^8455 ≤ (21453798806657/50000000000000 : ℝ)^6407
        have hw : |(2633377189/5000000000 : ℝ)|=(2633377189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391605633/10000000000 : ℝ)|^8455 ≤ (22127467760919/50000000000000 : ℝ)^6407
        have hw : |(5391605633/10000000000 : ℝ)|=(5391605633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312416883/10000000000 : ℝ)*x 0 + (-409832591/2000000000 : ℝ)*x 1 + (336975353/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312416883/10000000000 : ℝ)^8455 ≤ (10849798859589/25000000000000 : ℝ)^6407 := by
    have hnat : (5312416883 : ℕ)^8455*25000000000000^6407 ≤ 10849798859589^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312416883 10000000000 10849798859589 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409832591/2000000000 : ℝ)^8455 ≤ (12345868867417/100000000000000 : ℝ)^6407 := by
    have hnat : (409832591 : ℕ)^8455*100000000000000^6407 ≤ 12345868867417^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409832591 2000000000 12345868867417 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336975353/625000000 : ℝ)^8455 ≤ (11063733921079/25000000000000 : ℝ)^6407 := by
    have hnat : (336975353 : ℕ)^8455*25000000000000^6407 ≤ 11063733921079^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336975353 625000000 11063733921079 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312416883/10000000000 : ℝ), (-409832591/2000000000 : ℝ), (336975353/625000000 : ℝ)] ![(10849798859589/25000000000000 : ℝ), (12345868867417/100000000000000 : ℝ), (11063733921079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312416883/10000000000 : ℝ)|^8455 ≤ (10849798859589/25000000000000 : ℝ)^6407
        have hw : |(5312416883/10000000000 : ℝ)|=(5312416883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409832591/2000000000 : ℝ)|^8455 ≤ (12345868867417/100000000000000 : ℝ)^6407
        have hw : |(-409832591/2000000000 : ℝ)|=(409832591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336975353/625000000 : ℝ)|^8455 ≤ (11063733921079/25000000000000 : ℝ)^6407
        have hw : |(336975353/625000000 : ℝ)|=(336975353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312416869/10000000000 : ℝ)*x 0 + (5391605659/10000000000 : ℝ)*x 1 + (-25614537/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312416869/10000000000 : ℝ)^8455 ≤ (21699597643713/50000000000000 : ℝ)^6407 := by
    have hnat : (5312416869 : ℕ)^8455*50000000000000^6407 ≤ 21699597643713^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312416869 10000000000 21699597643713 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391605659/10000000000 : ℝ)^8455 ≤ (22127467901733/50000000000000 : ℝ)^6407 := by
    have hnat : (5391605659 : ℕ)^8455*50000000000000^6407 ≤ 22127467901733^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391605659 10000000000 22127467901733 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25614537/125000000 : ℝ)^8455 ≤ (1234586890717/10000000000000 : ℝ)^6407 := by
    have hnat : (25614537 : ℕ)^8455*10000000000000^6407 ≤ 1234586890717^6407*125000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25614537 125000000 1234586890717 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312416869/10000000000 : ℝ), (5391605659/10000000000 : ℝ), (-25614537/125000000 : ℝ)] ![(21699597643713/50000000000000 : ℝ), (22127467901733/50000000000000 : ℝ), (1234586890717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312416869/10000000000 : ℝ)|^8455 ≤ (21699597643713/50000000000000 : ℝ)^6407
        have hw : |(5312416869/10000000000 : ℝ)|=(5312416869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391605659/10000000000 : ℝ)|^8455 ≤ (22127467901733/50000000000000 : ℝ)^6407
        have hw : |(5391605659/10000000000 : ℝ)|=(5391605659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25614537/125000000 : ℝ)|^8455 ≤ (1234586890717/10000000000000 : ℝ)^6407
        have hw : |(-25614537/125000000 : ℝ)|=(25614537/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s5_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347992681/10000000000 : ℝ)*x 0 + (2238462553/5000000000 : ℝ)*x 1 + (1055669271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347992681/10000000000 : ℝ)^8455 ≤ (33317137591601/100000000000000 : ℝ)^6407 := by
    have hnat : (4347992681 : ℕ)^8455*100000000000000^6407 ≤ 33317137591601^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347992681 10000000000 33317137591601 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238462553/5000000000 : ℝ)^8455 ≤ (34627042350437/100000000000000 : ℝ)^6407 := by
    have hnat : (2238462553 : ℕ)^8455*100000000000000^6407 ≤ 34627042350437^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238462553 5000000000 34627042350437 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055669271/2500000000 : ℝ)^8455 ≤ (32055820038461/100000000000000 : ℝ)^6407 := by
    have hnat : (1055669271 : ℕ)^8455*100000000000000^6407 ≤ 32055820038461^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055669271 2500000000 32055820038461 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347992681/10000000000 : ℝ), (2238462553/5000000000 : ℝ), (1055669271/2500000000 : ℝ)] ![(33317137591601/100000000000000 : ℝ), (34627042350437/100000000000000 : ℝ), (32055820038461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347992681/10000000000 : ℝ)|^8455 ≤ (33317137591601/100000000000000 : ℝ)^6407
        have hw : |(4347992681/10000000000 : ℝ)|=(4347992681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238462553/5000000000 : ℝ)|^8455 ≤ (34627042350437/100000000000000 : ℝ)^6407
        have hw : |(2238462553/5000000000 : ℝ)|=(2238462553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055669271/2500000000 : ℝ)|^8455 ≤ (32055820038461/100000000000000 : ℝ)^6407
        have hw : |(1055669271/2500000000 : ℝ)|=(1055669271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (287/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7069/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1423/12500 : ℝ) ^ (4227/1024 : ℝ) ≤ (6359480682515351/50000000000000000000 : ℝ) := by
    have hpowers : (1423/12500 : ℝ)^4227 ≤ (6359480682515351/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1423 : ℕ)^4227*50000000000000000000^1024 ≤ 6359480682515351^1024*12500^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1423 12500 6359480682515351 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1423/12500 : ℝ)) (X := (6359480682515351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (4227/1024 : ℝ) ≤ (16012787945364497/50000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^4227 ≤ (16012787945364497/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7119 : ℕ)^4227*50000000000000000000^1024 ≤ 16012787945364497^1024*50000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 16012787945364497 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (16012787945364497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006359480682515351/25000000000000000000 : ℝ) ≤ (1000061617986191/1000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25006359480682515351/25000000000000000000 : ℝ)^1024 ≤ (1000061617986191/1000000000000000 : ℝ)^4227 := by
      have hnat : (25006359480682515351 : ℕ)^1024*1000000000000000^4227 ≤ 1000061617986191^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006359480682515351 25000000000000000000 1000061617986191 1000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000061617986191/1000000000000000 : ℝ)) (X := (25006359480682515351/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252796533578484981/6250000000000000000 : ℝ) ≤ (10001083762498299/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (6252796533578484981/6250000000000000000 : ℝ)^1024 ≤ (10001083762498299/10000000000000000 : ℝ)^4227 := by
      have hnat : (6252796533578484981 : ℕ)^1024*10000000000000000^4227 ≤ 10001083762498299^4227*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252796533578484981 6250000000000000000 10001083762498299 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001083762498299/10000000000000000 : ℝ)) (X := (6252796533578484981/6250000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016012787945364497/25000000000000000000 : ℝ) ≤ (312548479535459/312500000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25016012787945364497/25000000000000000000 : ℝ)^1024 ≤ (312548479535459/312500000000000 : ℝ)^4227 := by
      have hnat : (25016012787945364497 : ℕ)^1024*312500000000000^4227 ≤ 312548479535459^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016012787945364497 25000000000000000000 312548479535459 312500000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312548479535459/312500000000000 : ℝ)) (X := (25016012787945364497/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6359480682515351/50000000000000000000 : ℝ) ≤ ((7132778163965146597/7135000000000000000 : ℝ)+2*(467582636389/285400000000000 : ℝ)*(1423/12500 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (7132778163965146597/7135000000000000000 : ℝ)+2*(467582636389/285400000000000 : ℝ)*(1423/12500 : ℝ)=(1000061617986191/1000000000000000 : ℝ) by norm_num, show 1+2*(6359480682515351/50000000000000000000 : ℝ)=(25006359480682515351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16012787945364497/50000000000000000000 : ℝ)+(6359480682515351/50000000000000000000 : ℝ) ≤ ((7132778163965146597/7135000000000000000 : ℝ)+(467582636389/285400000000000 : ℝ)*((7119/50000 : ℝ)+(1423/12500 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (7132778163965146597/7135000000000000000 : ℝ)+(467582636389/285400000000000 : ℝ)*((7119/50000 : ℝ)+(1423/12500 : ℝ))=(10001083762498299/10000000000000000 : ℝ) by norm_num, show 1+(16012787945364497/50000000000000000000 : ℝ)+(6359480682515351/50000000000000000000 : ℝ)=(6252796533578484981/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16012787945364497/50000000000000000000 : ℝ) ≤ ((7132778163965146597/7135000000000000000 : ℝ)+2*(467582636389/285400000000000 : ℝ)*(7119/50000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (7132778163965146597/7135000000000000000 : ℝ)+2*(467582636389/285400000000000 : ℝ)*(7119/50000 : ℝ)=(312548479535459/312500000000000 : ℝ) by norm_num, show 1+2*(16012787945364497/50000000000000000000 : ℝ)=(25016012787945364497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7132778163965146597/7135000000000000000 : ℝ)*(X 1 0+X 2 0)+(467582636389/285400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (7132778163965146597/7135000000000000000 : ℝ)) (alpha := (467582636389/285400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7132778163965146597/7135000000000000000 : ℝ)*(X 0 1+X 2 1)+(467582636389/285400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (7132778163965146597/7135000000000000000 : ℝ)) (alpha := (467582636389/285400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7132778163965146597/7135000000000000000 : ℝ)*(X 0 2+X 1 2)+(467582636389/285400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (7132778163965146597/7135000000000000000 : ℝ)) (alpha := (467582636389/285400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527673917/2500000000 : ℝ)*X 0 0+(2695964551/5000000000 : ℝ)*X 0 1+(1316608029/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344480529/10000000000 : ℝ)*X 1 0+(-2174336551/10000000000 : ℝ)*X 1 1+(329152009/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668060087/1250000000 : ℝ)*X 2 0+(2633216057/5000000000 : ℝ)*X 2 1+(-135896023/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173919311/400000000 : ℝ)*X 0 0+(4222018591/10000000000 : ℝ)*X 0 1+(4477581189/10000000000 : ℝ)*X 0 2+(173919311/400000000 : ℝ)*X 1 0+(4222018591/10000000000 : ℝ)*X 1 1+(4477581189/10000000000 : ℝ)*X 1 2+(173919311/400000000 : ℝ)*X 2 0+(4222018591/10000000000 : ℝ)*X 2 1+(4477581189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42214011/200000000 : ℝ)*X 0 0+(2633377189/5000000000 : ℝ)*X 0 1+(5391605633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312416883/10000000000 : ℝ)*X 1 0+(-409832591/2000000000 : ℝ)*X 1 1+(336975353/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312416869/10000000000 : ℝ)*X 2 0+(5391605659/10000000000 : ℝ)*X 2 1+(-25614537/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347992681/10000000000 : ℝ)*X 0 0+(2238462553/5000000000 : ℝ)*X 0 1+(1055669271/2500000000 : ℝ)*X 0 2+(4347992681/10000000000 : ℝ)*X 1 0+(2238462553/5000000000 : ℝ)*X 1 1+(1055669271/2500000000 : ℝ)*X 1 2+(4347992681/10000000000 : ℝ)*X 2 0+(2238462553/5000000000 : ℝ)*X 2 1+(1055669271/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (813171637335655998931354911/178375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3148097/390625000000 : ℝ)*(base19) + (994630369/100000000000000 : ℝ)*(base23) + (4505451/10000000000000 : ℝ)*(lower2) + (183226627/100000000000000 : ℝ)*(upper5) + (2970334214497679/50000000000000 : ℝ)*(major0) + (2970334214497679/50000000000000 : ℝ)*(major1) + (2970334214497679/50000000000000 : ℝ)*(major2) + (996042694065933/12500000000000 : ℝ)*(sp0) + (7968373005495707/100000000000000 : ℝ)*(sp1) + (7968376822042033/100000000000000 : ℝ)*(sp2) + (3912948150938923/100000000000000 : ℝ)*(sp3) + (18132072469/50000000000000 : ℝ)*(sp4) + (500657983/12500000000000 : ℝ)*(sp5) + (10738420187/100000000000000 : ℝ)*(sp7) + (391295888935911/10000000000000 : ℝ)*(f.failure) + (7968377816672403/100000000000000 : ℝ)*(f.sum) + (3553494990431/7135000000000000000000000000 : ℝ)*base65 + (7676375678132273363/356750000000000000000000000000000 : ℝ)*base67 + (4379308044231773363/356750000000000000000000000000000 : ℝ)*base69 + (2066744865682726637/356750000000000000000000000000000 : ℝ)*base72 + (10482815644001/7135000000000000000000000000 : ℝ)*base73 + (868659687843273363/356750000000000000000000000000000 : ℝ)*base75 + (3416113757909523363/356750000000000000000000000000000 : ℝ)*base77 + (4529879751490226637/356750000000000000000000000000000 : ℝ)*base80 + (7914356233677/3567500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (172901/250000000000000000000 : ℝ)*base89 + (172901/250000000000000000000 : ℝ)*base91 + (172901/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29842960510996545316041/14270000000000000000000000000 : ℝ) := by norm_num
    linear_combination (424291643/100000000000000 : ℝ)*(base19) + (86430317/20000000000000 : ℝ)*(base23) + (28135849/50000000000000 : ℝ)*(upper3) + (6855581/50000000000000 : ℝ)*(lower4) + (12721281/25000000000000 : ℝ)*(upper5) + (5971348662102181/100000000000000 : ℝ)*(major0) + (5971348662102181/100000000000000 : ℝ)*(major1) + (5971348662102181/100000000000000 : ℝ)*(major2) + (3021264749/25000000000000 : ℝ)*(sp1) + (12608231059/100000000000000 : ℝ)*(sp2) + (1601906023764871/20000000000000 : ℝ)*(sp4) + (2002379402368429/25000000000000 : ℝ)*(sp5) + (500594817402607/6250000000000 : ℝ)*(sp6) + (786633427133949/20000000000000 : ℝ)*(sp7) + (786633427133949/20000000000000 : ℝ)*(f.failure) + (1601906023764871/20000000000000 : ℝ)*(f.sum) + (37191623561241/14270000000000000000000000000 : ℝ)*base66 + (8986416264308653057/713500000000000000000000000000000 : ℝ)*base67 + (127014384486153057/713500000000000000000000000000000 : ℝ)*base69 + (319463350600846943/713500000000000000000000000000000 : ℝ)*base72 + (91507857037971/14270000000000000000000000000 : ℝ)*base74 + (1591324559053346943/713500000000000000000000000000000 : ℝ)*base76 + (5338037325780846943/713500000000000000000000000000000 : ℝ)*base78 + (2378406833464653057/713500000000000000000000000000000 : ℝ)*base79 + (21239779241551/14270000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1515641/500000000000000000000 : ℝ)*base90 + (1515641/500000000000000000000 : ℝ)*base92 + (1515641/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1262_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1262_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1262_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1262_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7069/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

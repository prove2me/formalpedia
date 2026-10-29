-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:12.535389+00:00
-- url     : https://prove2.me/submissions/8caf28f1-7d46-4b1b-8410-ec07647ecc07

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
theorem support_rectangle_w1446_s0_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-437307127/2500000000 : ℝ)*x 0 + (5953197141/10000000000 : ℝ)*x 1 + (2417555057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437307127/2500000000 : ℝ)^2203 ≤ (206360256247/2000000000000 : ℝ)^1691 := by
    have hnat : (437307127 : ℕ)^2203*2000000000000^1691 ≤ 206360256247^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437307127 2500000000 206360256247 2000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5953197141/10000000000 : ℝ)^2203 ≤ (3180015944221/6250000000000 : ℝ)^1691 := by
    have hnat : (5953197141 : ℕ)^2203*6250000000000^1691 ≤ 3180015944221^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5953197141 10000000000 3180015944221 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417555057/5000000000 : ℝ)^2203 ≤ (19400866031407/50000000000000 : ℝ)^1691 := by
    have hnat : (2417555057 : ℕ)^2203*50000000000000^1691 ≤ 19400866031407^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417555057 5000000000 19400866031407 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437307127/2500000000 : ℝ), (5953197141/10000000000 : ℝ), (2417555057/5000000000 : ℝ)] ![(206360256247/2000000000000 : ℝ), (3180015944221/6250000000000 : ℝ), (19400866031407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437307127/2500000000 : ℝ)|^2203 ≤ (206360256247/2000000000000 : ℝ)^1691
        have hw : |(-437307127/2500000000 : ℝ)|=(437307127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5953197141/10000000000 : ℝ)|^2203 ≤ (3180015944221/6250000000000 : ℝ)^1691
        have hw : |(5953197141/10000000000 : ℝ)|=(5953197141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417555057/5000000000 : ℝ)|^2203 ≤ (19400866031407/50000000000000 : ℝ)^1691
        have hw : |(2417555057/5000000000 : ℝ)|=(2417555057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (343138167/625000000 : ℝ)*x 0 + (-595023051/2500000000 : ℝ)*x 1 + (604388747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343138167/625000000 : ℝ)^2203 ≤ (45786971719889/100000000000000 : ℝ)^1691 := by
    have hnat : (343138167 : ℕ)^2203*100000000000000^1691 ≤ 45786971719889^1691*625000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343138167 625000000 45786971719889 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595023051/2500000000 : ℝ)^2203 ≤ (15411297649033/100000000000000 : ℝ)^1691 := by
    have hnat : (595023051 : ℕ)^2203*100000000000000^1691 ≤ 15411297649033^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595023051 2500000000 15411297649033 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604388747/1250000000 : ℝ)^2203 ≤ (9700432655013/25000000000000 : ℝ)^1691 := by
    have hnat : (604388747 : ℕ)^2203*25000000000000^1691 ≤ 9700432655013^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604388747 1250000000 9700432655013 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343138167/625000000 : ℝ), (-595023051/2500000000 : ℝ), (604388747/1250000000 : ℝ)] ![(45786971719889/100000000000000 : ℝ), (15411297649033/100000000000000 : ℝ), (9700432655013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343138167/625000000 : ℝ)|^2203 ≤ (45786971719889/100000000000000 : ℝ)^1691
        have hw : |(343138167/625000000 : ℝ)|=(343138167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-595023051/2500000000 : ℝ)|^2203 ≤ (15411297649033/100000000000000 : ℝ)^1691
        have hw : |(-595023051/2500000000 : ℝ)|=(595023051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604388747/1250000000 : ℝ)|^2203 ≤ (9700432655013/25000000000000 : ℝ)^1691
        have hw : |(604388747/1250000000 : ℝ)|=(604388747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5490210557/10000000000 : ℝ)*x 0 + (2417554969/5000000000 : ℝ)*x 1 + (-5950231/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5490210557/10000000000 : ℝ)^2203 ≤ (45786970470431/100000000000000 : ℝ)^1691 := by
    have hnat : (5490210557 : ℕ)^2203*100000000000000^1691 ≤ 45786970470431^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490210557 10000000000 45786970470431 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417554969/5000000000 : ℝ)^2203 ≤ (3880173022277/10000000000000 : ℝ)^1691 := by
    have hnat : (2417554969 : ℕ)^2203*10000000000000^1691 ≤ 3880173022277^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417554969 5000000000 3880173022277 10000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5950231/25000000 : ℝ)^2203 ≤ (3852824825603/25000000000000 : ℝ)^1691 := by
    have hnat : (5950231 : ℕ)^2203*25000000000000^1691 ≤ 3852824825603^1691*25000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5950231 25000000 3852824825603 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5490210557/10000000000 : ℝ), (2417554969/5000000000 : ℝ), (-5950231/25000000 : ℝ)] ![(45786970470431/100000000000000 : ℝ), (3880173022277/10000000000000 : ℝ), (3852824825603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5490210557/10000000000 : ℝ)|^2203 ≤ (45786970470431/100000000000000 : ℝ)^1691
        have hw : |(5490210557/10000000000 : ℝ)|=(5490210557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417554969/5000000000 : ℝ)|^2203 ≤ (3880173022277/10000000000000 : ℝ)^1691
        have hw : |(2417554969/5000000000 : ℝ)|=(2417554969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5950231/25000000 : ℝ)|^2203 ≤ (3852824825603/25000000000000 : ℝ)^1691
        have hw : |(-5950231/25000000 : ℝ)|=(5950231/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (520446593/1250000000 : ℝ)*x 0 + (620595203/2000000000 : ℝ)*x 1 + (1107369297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520446593/1250000000 : ℝ)^2203 ≤ (15966816887481/50000000000000 : ℝ)^1691 := by
    have hnat : (520446593 : ℕ)^2203*50000000000000^1691 ≤ 15966816887481^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520446593 1250000000 15966816887481 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620595203/2000000000 : ℝ)^2203 ≤ (21772052995817/100000000000000 : ℝ)^1691 := by
    have hnat : (620595203 : ℕ)^2203*100000000000000^1691 ≤ 21772052995817^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620595203 2000000000 21772052995817 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107369297/2000000000 : ℝ)^2203 ≤ (9258862642359/20000000000000 : ℝ)^1691 := by
    have hnat : (1107369297 : ℕ)^2203*20000000000000^1691 ≤ 9258862642359^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107369297 2000000000 9258862642359 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520446593/1250000000 : ℝ), (620595203/2000000000 : ℝ), (1107369297/2000000000 : ℝ)] ![(15966816887481/50000000000000 : ℝ), (21772052995817/100000000000000 : ℝ), (9258862642359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520446593/1250000000 : ℝ)|^2203 ≤ (15966816887481/50000000000000 : ℝ)^1691
        have hw : |(520446593/1250000000 : ℝ)|=(520446593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620595203/2000000000 : ℝ)|^2203 ≤ (21772052995817/100000000000000 : ℝ)^1691
        have hw : |(620595203/2000000000 : ℝ)|=(620595203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107369297/2000000000 : ℝ)|^2203 ≤ (9258862642359/20000000000000 : ℝ)^1691
        have hw : |(1107369297/2000000000 : ℝ)|=(1107369297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-876582631/5000000000 : ℝ)*x 0 + (4863679121/10000000000 : ℝ)*x 1 + (5923607899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (876582631/5000000000 : ℝ)^2203 ≤ (517413771707/5000000000000 : ℝ)^1691 := by
    have hnat : (876582631 : ℕ)^2203*5000000000000^1691 ≤ 517413771707^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876582631 5000000000 517413771707 5000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4863679121/10000000000 : ℝ)^2203 ≤ (2443792628753/6250000000000 : ℝ)^1691 := by
    have hnat : (4863679121 : ℕ)^2203*6250000000000^1691 ≤ 2443792628753^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863679121 10000000000 2443792628753 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5923607899/10000000000 : ℝ)^2203 ≤ (50551042501369/100000000000000 : ℝ)^1691 := by
    have hnat : (5923607899 : ℕ)^2203*100000000000000^1691 ≤ 50551042501369^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923607899 10000000000 50551042501369 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-876582631/5000000000 : ℝ), (4863679121/10000000000 : ℝ), (5923607899/10000000000 : ℝ)] ![(517413771707/5000000000000 : ℝ), (2443792628753/6250000000000 : ℝ), (50551042501369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-876582631/5000000000 : ℝ)|^2203 ≤ (517413771707/5000000000000 : ℝ)^1691
        have hw : |(-876582631/5000000000 : ℝ)|=(876582631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4863679121/10000000000 : ℝ)|^2203 ≤ (2443792628753/6250000000000 : ℝ)^1691
        have hw : |(4863679121/10000000000 : ℝ)|=(4863679121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5923607899/10000000000 : ℝ)|^2203 ≤ (50551042501369/100000000000000 : ℝ)^1691
        have hw : |(5923607899/10000000000 : ℝ)|=(5923607899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5184966057/10000000000 : ℝ)*x 0 + (-161449307/1250000000 : ℝ)*x 1 + (5923607967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184966057/10000000000 : ℝ)^2203 ≤ (42498818052363/100000000000000 : ℝ)^1691 := by
    have hnat : (5184966057 : ℕ)^2203*100000000000000^1691 ≤ 42498818052363^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184966057 10000000000 42498818052363 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161449307/1250000000 : ℝ)^2203 ≤ (6950138669671/100000000000000 : ℝ)^1691 := by
    have hnat : (161449307 : ℕ)^2203*100000000000000^1691 ≤ 6950138669671^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161449307 1250000000 6950138669671 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5923607967/10000000000 : ℝ)^2203 ≤ (12637760814343/25000000000000 : ℝ)^1691 := by
    have hnat : (5923607967 : ℕ)^2203*25000000000000^1691 ≤ 12637760814343^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923607967 10000000000 12637760814343 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184966057/10000000000 : ℝ), (-161449307/1250000000 : ℝ), (5923607967/10000000000 : ℝ)] ![(42498818052363/100000000000000 : ℝ), (6950138669671/100000000000000 : ℝ), (12637760814343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184966057/10000000000 : ℝ)|^2203 ≤ (42498818052363/100000000000000 : ℝ)^1691
        have hw : |(5184966057/10000000000 : ℝ)|=(5184966057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161449307/1250000000 : ℝ)|^2203 ≤ (6950138669671/100000000000000 : ℝ)^1691
        have hw : |(-161449307/1250000000 : ℝ)|=(161449307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5923607967/10000000000 : ℝ)|^2203 ≤ (12637760814343/25000000000000 : ℝ)^1691
        have hw : |(5923607967/10000000000 : ℝ)|=(5923607967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2592483043/5000000000 : ℝ)*x 0 + (5923607813/10000000000 : ℝ)*x 1 + (-40362333/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592483043/5000000000 : ℝ)^2203 ≤ (42498818362033/100000000000000 : ℝ)^1691 := by
    have hnat : (2592483043 : ℕ)^2203*100000000000000^1691 ≤ 42498818362033^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592483043 5000000000 42498818362033 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5923607813/10000000000 : ℝ)^2203 ≤ (1579720048289/3125000000000 : ℝ)^1691 := by
    have hnat : (5923607813 : ℕ)^2203*3125000000000^1691 ≤ 1579720048289^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923607813 10000000000 1579720048289 3125000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40362333/312500000 : ℝ)^2203 ≤ (6950140071737/100000000000000 : ℝ)^1691 := by
    have hnat : (40362333 : ℕ)^2203*100000000000000^1691 ≤ 6950140071737^1691*312500000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40362333 312500000 6950140071737 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592483043/5000000000 : ℝ), (5923607813/10000000000 : ℝ), (-40362333/312500000 : ℝ)] ![(42498818362033/100000000000000 : ℝ), (1579720048289/3125000000000 : ℝ), (6950140071737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592483043/5000000000 : ℝ)|^2203 ≤ (42498818362033/100000000000000 : ℝ)^1691
        have hw : |(2592483043/5000000000 : ℝ)|=(2592483043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5923607813/10000000000 : ℝ)|^2203 ≤ (1579720048289/3125000000000 : ℝ)^1691
        have hw : |(5923607813/10000000000 : ℝ)|=(5923607813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40362333/312500000 : ℝ)|^2203 ≤ (6950140071737/100000000000000 : ℝ)^1691
        have hw : |(-40362333/312500000 : ℝ)|=(40362333/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s0_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2086070739/5000000000 : ℝ)*x 0 + (1368664149/2500000000 : ℝ)*x 1 + (316738661/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086070739/5000000000 : ℝ)^2203 ≤ (16009639677889/50000000000000 : ℝ)^1691 := by
    have hnat : (2086070739 : ℕ)^2203*50000000000000^1691 ≤ 16009639677889^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086070739 5000000000 16009639677889 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368664149/2500000000 : ℝ)^2203 ≤ (114045128799/250000000000 : ℝ)^1691 := by
    have hnat : (1368664149 : ℕ)^2203*250000000000^1691 ≤ 114045128799^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368664149 2500000000 114045128799 250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316738661/1000000000 : ℝ)^2203 ≤ (5590667276453/25000000000000 : ℝ)^1691 := by
    have hnat : (316738661 : ℕ)^2203*25000000000000^1691 ≤ 5590667276453^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316738661 1000000000 5590667276453 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086070739/5000000000 : ℝ), (1368664149/2500000000 : ℝ), (316738661/1000000000 : ℝ)] ![(16009639677889/50000000000000 : ℝ), (114045128799/250000000000 : ℝ), (5590667276453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086070739/5000000000 : ℝ)|^2203 ≤ (16009639677889/50000000000000 : ℝ)^1691
        have hw : |(2086070739/5000000000 : ℝ)|=(2086070739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368664149/2500000000 : ℝ)|^2203 ≤ (114045128799/250000000000 : ℝ)^1691
        have hw : |(1368664149/2500000000 : ℝ)|=(1368664149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316738661/1000000000 : ℝ)|^2203 ≤ (5590667276453/25000000000000 : ℝ)^1691
        have hw : |(316738661/1000000000 : ℝ)|=(316738661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26141/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4405/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4405 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4405*1^1024 ≤ 0^1024*1^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4405/1024 : ℝ) ≤ (1941594167824558419/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4405 ≤ (1941594167824558419/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4405*100000000000000000000^1024 ≤ 1941594167824558419^1024*5^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1941594167824558419 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1941594167824558419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4405 := by
      have hnat : (1 : ℕ)^1024*1^4405 ≤ 1^4405*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101941594167824558419/100000000000000000000 : ℝ) ≤ (2511200596952743/2500000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (101941594167824558419/100000000000000000000 : ℝ)^1024 ≤ (2511200596952743/2500000000000000 : ℝ)^4405 := by
      have hnat : (101941594167824558419 : ℕ)^1024*2500000000000000^4405 ≤ 2511200596952743^4405*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101941594167824558419 100000000000000000000 2511200596952743 2500000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511200596952743/2500000000000000 : ℝ)) (X := (101941594167824558419/100000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51941594167824558419/50000000000000000000 : ℝ) ≤ (1261200596952743/1250000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (51941594167824558419/50000000000000000000 : ℝ)^1024 ≤ (1261200596952743/1250000000000000 : ℝ)^4405 := by
      have hnat : (51941594167824558419 : ℕ)^1024*1250000000000000^4405 ≤ 1261200596952743^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51941594167824558419 50000000000000000000 1261200596952743 1250000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261200596952743/1250000000000000 : ℝ)) (X := (51941594167824558419/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11200596952743/1000000000000000 : ℝ)*(0 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11200596952743/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1941594167824558419/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11200596952743/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11200596952743/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511200596952743/2500000000000000 : ℝ) by norm_num, show 1+(1941594167824558419/100000000000000000000 : ℝ)+(0 : ℝ)=(101941594167824558419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1941594167824558419/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11200596952743/1000000000000000 : ℝ)*(2/5 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11200596952743/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261200596952743/1250000000000000 : ℝ) by norm_num, show 1+2*(1941594167824558419/100000000000000000000 : ℝ)=(51941594167824558419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11200596952743/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11200596952743/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11200596952743/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11200596952743/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11200596952743/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11200596952743/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437307127/2500000000 : ℝ)*X 0 0+(5953197141/10000000000 : ℝ)*X 0 1+(2417555057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343138167/625000000 : ℝ)*X 1 0+(-595023051/2500000000 : ℝ)*X 1 1+(604388747/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5490210557/10000000000 : ℝ)*X 2 0+(2417554969/5000000000 : ℝ)*X 2 1+(-5950231/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((520446593/1250000000 : ℝ)*X 0 0+(620595203/2000000000 : ℝ)*X 0 1+(1107369297/2000000000 : ℝ)*X 0 2+(520446593/1250000000 : ℝ)*X 1 0+(620595203/2000000000 : ℝ)*X 1 1+(1107369297/2000000000 : ℝ)*X 1 2+(520446593/1250000000 : ℝ)*X 2 0+(620595203/2000000000 : ℝ)*X 2 1+(1107369297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-876582631/5000000000 : ℝ)*X 0 0+(4863679121/10000000000 : ℝ)*X 0 1+(5923607899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184966057/10000000000 : ℝ)*X 1 0+(-161449307/1250000000 : ℝ)*X 1 1+(5923607967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592483043/5000000000 : ℝ)*X 2 0+(5923607813/10000000000 : ℝ)*X 2 1+(-40362333/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086070739/5000000000 : ℝ)*X 0 0+(1368664149/2500000000 : ℝ)*X 0 1+(316738661/1000000000 : ℝ)*X 0 2+(2086070739/5000000000 : ℝ)*X 1 0+(1368664149/2500000000 : ℝ)*X 1 1+(316738661/1000000000 : ℝ)*X 1 2+(2086070739/5000000000 : ℝ)*X 2 0+(1368664149/2500000000 : ℝ)*X 2 1+(316738661/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61729941198305980157919/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14442671/10000000000000 : ℝ)*(base1) + (1114696383/100000000000000 : ℝ)*(base19) + (547981077/50000000000000 : ℝ)*(base23) + (73295407/50000000000000 : ℝ)*(upper3) + (88151361/100000000000000 : ℝ)*(upper5) + (326315684445611/50000000000000 : ℝ)*(major0) + (326315684445611/50000000000000 : ℝ)*(major1) + (326315684445611/50000000000000 : ℝ)*(major2) + (894388189886087/100000000000000 : ℝ)*(sp0) + (447195059151873/50000000000000 : ℝ)*(sp1) + (35775605481519/4000000000000 : ℝ)*(sp2) + (410869585413429/100000000000000 : ℝ)*(sp3) + (199221297/6250000000000 : ℝ)*(sp4) + (402582249/25000000000000 : ℝ)*(sp7) + (82174268033827/20000000000000 : ℝ)*(f.failure) + (894391233000129/100000000000000 : ℝ)*(f.sum) + (46193830339027/25000000000000000000000000000 : ℝ)*base66 + (183594044739027/50000000000000000000000000000 : ℝ)*base68 + (40508808789027/50000000000000000000000000000 : ℝ)*base70 + (204092708039027/50000000000000000000000000000 : ℝ)*base72 + (2710749085973/25000000000000000000000000000 : ℝ)*base73 + (229988115289027/50000000000000000000000000000 : ℝ)*base76 + (115498946189027/50000000000000000000000000000 : ℝ)*base78 + (369733009289027/50000000000000000000000000000 : ℝ)*base80 + (45762405135973/25000000000000000000000000000 : ℝ)*base81 + (16113697/2000000000000000000000 : ℝ)*base89 + (16113697/2000000000000000000000 : ℝ)*base91 + (16113697/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45809541870583423576707/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209732561/25000000000000 : ℝ)*(base19) + (846266737/100000000000000 : ℝ)*(base23) + (26301539/25000000000000 : ℝ)*(base32) + (64760231/50000000000000 : ℝ)*(upper3) + (67725881/100000000000000 : ℝ)*(upper5) + (172108971912117/25000000000000 : ℝ)*(major0) + (172108971912117/25000000000000 : ℝ)*(major1) + (172108971912117/25000000000000 : ℝ)*(major2) + (2010806807/100000000000000 : ℝ)*(sp1) + (2045793407/100000000000000 : ℝ)*(sp2) + (117932397473191/12500000000000 : ℝ)*(sp4) + (471728165024239/50000000000000 : ℝ)*(sp5) + (117932035965673/12500000000000 : ℝ)*(sp6) + (108353092036617/25000000000000 : ℝ)*(sp7) + (3467299786821/800000000000 : ℝ)*(f.failure) + (117932397473191/12500000000000 : ℝ)*(f.sum) + (27972305986931/12500000000000000000000000000 : ℝ)*base65 + (60201602686931/25000000000000000000000000000 : ℝ)*base67 + (12968780713069/25000000000000000000000000000 : ℝ)*base70 + (7705683263069/25000000000000000000000000000 : ℝ)*base72 + (15205293936931/12500000000000000000000000000 : ℝ)*base73 + (96087410363069/25000000000000000000000000000 : ℝ)*base76 + (93355087411931/25000000000000000000000000000 : ℝ)*base77 + (156455525936931/25000000000000000000000000000 : ℝ)*base79 + (23267286613069/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (351831/80000000000000000000 : ℝ)*base89 + (351831/80000000000000000000 : ℝ)*base91 + (351831/80000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1446_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26141/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1446_s1_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1919182559/10000000000 : ℝ)*x 0 + (279924219/500000000 : ℝ)*x 1 + (1270209901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919182559/10000000000 : ℝ)^2203 ≤ (11642832605337/100000000000000 : ℝ)^1691 := by
    have hnat : (1919182559 : ℕ)^2203*100000000000000^1691 ≤ 11642832605337^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919182559 10000000000 11642832605337 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279924219/500000000 : ℝ)^2203 ≤ (46966845713959/100000000000000 : ℝ)^1691 := by
    have hnat : (279924219 : ℕ)^2203*100000000000000^1691 ≤ 46966845713959^1691*500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279924219 500000000 46966845713959 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270209901/2500000000 : ℝ)^2203 ≤ (20695160832441/50000000000000 : ℝ)^1691 := by
    have hnat : (1270209901 : ℕ)^2203*50000000000000^1691 ≤ 20695160832441^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270209901 2500000000 20695160832441 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1919182559/10000000000 : ℝ), (279924219/500000000 : ℝ), (1270209901/2500000000 : ℝ)] ![(11642832605337/100000000000000 : ℝ), (46966845713959/100000000000000 : ℝ), (20695160832441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1919182559/10000000000 : ℝ)|^2203 ≤ (11642832605337/100000000000000 : ℝ)^1691
        have hw : |(-1919182559/10000000000 : ℝ)|=(1919182559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(279924219/500000000 : ℝ)|^2203 ≤ (46966845713959/100000000000000 : ℝ)^1691
        have hw : |(279924219/500000000 : ℝ)|=(279924219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270209901/2500000000 : ℝ)|^2203 ≤ (20695160832441/50000000000000 : ℝ)^1691
        have hw : |(1270209901/2500000000 : ℝ)|=(1270209901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5395110683/10000000000 : ℝ)*x 0 + (-548281399/2500000000 : ℝ)*x 1 + (158776243/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395110683/10000000000 : ℝ)^2203 ≤ (44756444954297/100000000000000 : ℝ)^1691 := by
    have hnat : (5395110683 : ℕ)^2203*100000000000000^1691 ≤ 44756444954297^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395110683 10000000000 44756444954297 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548281399/2500000000 : ℝ)^2203 ≤ (6926615771413/50000000000000 : ℝ)^1691 := by
    have hnat : (548281399 : ℕ)^2203*50000000000000^1691 ≤ 6926615771413^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548281399 2500000000 6926615771413 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158776243/312500000 : ℝ)^2203 ≤ (41390323490301/100000000000000 : ℝ)^1691 := by
    have hnat : (158776243 : ℕ)^2203*100000000000000^1691 ≤ 41390323490301^1691*312500000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158776243 312500000 41390323490301 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395110683/10000000000 : ℝ), (-548281399/2500000000 : ℝ), (158776243/312500000 : ℝ)] ![(44756444954297/100000000000000 : ℝ), (6926615771413/50000000000000 : ℝ), (41390323490301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395110683/10000000000 : ℝ)|^2203 ≤ (44756444954297/100000000000000 : ℝ)^1691
        have hw : |(5395110683/10000000000 : ℝ)|=(5395110683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548281399/2500000000 : ℝ)|^2203 ≤ (6926615771413/50000000000000 : ℝ)^1691
        have hw : |(-548281399/2500000000 : ℝ)|=(548281399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158776243/312500000 : ℝ)|^2203 ≤ (41390323490301/100000000000000 : ℝ)^1691
        have hw : |(158776243/312500000 : ℝ)|=(158776243/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2697555377/5000000000 : ℝ)*x 0 + (5080839633/10000000000 : ℝ)*x 1 + (-2193125687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697555377/5000000000 : ℝ)^2203 ≤ (44756445721631/100000000000000 : ℝ)^1691 := by
    have hnat : (2697555377 : ℕ)^2203*100000000000000^1691 ≤ 44756445721631^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697555377 5000000000 44756445721631 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080839633/10000000000 : ℝ)^2203 ≤ (2586895123291/6250000000000 : ℝ)^1691 := by
    have hnat : (5080839633 : ℕ)^2203*6250000000000^1691 ≤ 2586895123291^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080839633 10000000000 2586895123291 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193125687/10000000000 : ℝ)^2203 ≤ (2770646458337/20000000000000 : ℝ)^1691 := by
    have hnat : (2193125687 : ℕ)^2203*20000000000000^1691 ≤ 2770646458337^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193125687 10000000000 2770646458337 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697555377/5000000000 : ℝ), (5080839633/10000000000 : ℝ), (-2193125687/10000000000 : ℝ)] ![(44756445721631/100000000000000 : ℝ), (2586895123291/6250000000000 : ℝ), (2770646458337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697555377/5000000000 : ℝ)|^2203 ≤ (44756445721631/100000000000000 : ℝ)^1691
        have hw : |(2697555377/5000000000 : ℝ)|=(2697555377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080839633/10000000000 : ℝ)|^2203 ≤ (2586895123291/6250000000000 : ℝ)^1691
        have hw : |(5080839633/10000000000 : ℝ)|=(5080839633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193125687/10000000000 : ℝ)|^2203 ≤ (2770646458337/20000000000000 : ℝ)^1691
        have hw : |(-2193125687/10000000000 : ℝ)|=(2193125687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534193227/1250000000 : ℝ)*x 0 + (3743052613/10000000000 : ℝ)*x 1 + (973973951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534193227/1250000000 : ℝ)^2203 ≤ (33036853633357/100000000000000 : ℝ)^1691 := by
    have hnat : (534193227 : ℕ)^2203*100000000000000^1691 ≤ 33036853633357^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534193227 1250000000 33036853633357 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3743052613/10000000000 : ℝ)^2203 ≤ (27797614423867/100000000000000 : ℝ)^1691 := by
    have hnat : (3743052613 : ℕ)^2203*100000000000000^1691 ≤ 27797614423867^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743052613 10000000000 27797614423867 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973973951/2000000000 : ℝ)^2203 ≤ (7833106385397/20000000000000 : ℝ)^1691 := by
    have hnat : (973973951 : ℕ)^2203*20000000000000^1691 ≤ 7833106385397^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973973951 2000000000 7833106385397 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534193227/1250000000 : ℝ), (3743052613/10000000000 : ℝ), (973973951/2000000000 : ℝ)] ![(33036853633357/100000000000000 : ℝ), (27797614423867/100000000000000 : ℝ), (7833106385397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534193227/1250000000 : ℝ)|^2203 ≤ (33036853633357/100000000000000 : ℝ)^1691
        have hw : |(534193227/1250000000 : ℝ)|=(534193227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3743052613/10000000000 : ℝ)|^2203 ≤ (27797614423867/100000000000000 : ℝ)^1691
        have hw : |(3743052613/10000000000 : ℝ)|=(3743052613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(973973951/2000000000 : ℝ)|^2203 ≤ (7833106385397/20000000000000 : ℝ)^1691
        have hw : |(973973951/2000000000 : ℝ)|=(973973951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-47988949/250000000 : ℝ)*x 0 + (1271707101/2500000000 : ℝ)*x 1 + (5592395429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47988949/250000000 : ℝ)^2203 ≤ (11645799632619/100000000000000 : ℝ)^1691 := by
    have hnat : (47988949 : ℕ)^2203*100000000000000^1691 ≤ 11645799632619^1691*250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47988949 250000000 11645799632619 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271707101/2500000000 : ℝ)^2203 ≤ (20726945779259/50000000000000 : ℝ)^1691 := by
    have hnat : (1271707101 : ℕ)^2203*50000000000000^1691 ≤ 20726945779259^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271707101 2500000000 20726945779259 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592395429/10000000000 : ℝ)^2203 ≤ (46900308783733/100000000000000 : ℝ)^1691 := by
    have hnat : (5592395429 : ℕ)^2203*100000000000000^1691 ≤ 46900308783733^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592395429 10000000000 46900308783733 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47988949/250000000 : ℝ), (1271707101/2500000000 : ℝ), (5592395429/10000000000 : ℝ)] ![(11645799632619/100000000000000 : ℝ), (20726945779259/50000000000000 : ℝ), (46900308783733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47988949/250000000 : ℝ)|^2203 ≤ (11645799632619/100000000000000 : ℝ)^1691
        have hw : |(-47988949/250000000 : ℝ)|=(47988949/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271707101/2500000000 : ℝ)|^2203 ≤ (20726945779259/50000000000000 : ℝ)^1691
        have hw : |(1271707101/2500000000 : ℝ)|=(1271707101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592395429/10000000000 : ℝ)|^2203 ≤ (46900308783733/100000000000000 : ℝ)^1691
        have hw : |(5592395429/10000000000 : ℝ)|=(5592395429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5259695509/10000000000 : ℝ)*x 0 + (-336313919/2000000000 : ℝ)*x 1 + (2796197729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259695509/10000000000 : ℝ)^2203 ≤ (43298536371163/100000000000000 : ℝ)^1691 := by
    have hnat : (5259695509 : ℕ)^2203*100000000000000^1691 ≤ 43298536371163^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259695509 10000000000 43298536371163 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336313919/2000000000 : ℝ)^2203 ≤ (9801154516943/100000000000000 : ℝ)^1691 := by
    have hnat : (336313919 : ℕ)^2203*100000000000000^1691 ≤ 9801154516943^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336313919 2000000000 9801154516943 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2796197729/5000000000 : ℝ)^2203 ≤ (23450154550289/50000000000000 : ℝ)^1691 := by
    have hnat : (2796197729 : ℕ)^2203*50000000000000^1691 ≤ 23450154550289^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796197729 5000000000 23450154550289 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259695509/10000000000 : ℝ), (-336313919/2000000000 : ℝ), (2796197729/5000000000 : ℝ)] ![(43298536371163/100000000000000 : ℝ), (9801154516943/100000000000000 : ℝ), (23450154550289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259695509/10000000000 : ℝ)|^2203 ≤ (43298536371163/100000000000000 : ℝ)^1691
        have hw : |(5259695509/10000000000 : ℝ)|=(5259695509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336313919/2000000000 : ℝ)|^2203 ≤ (9801154516943/100000000000000 : ℝ)^1691
        have hw : |(-336313919/2000000000 : ℝ)|=(336313919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2796197729/5000000000 : ℝ)|^2203 ≤ (23450154550289/50000000000000 : ℝ)^1691
        have hw : |(2796197729/5000000000 : ℝ)|=(2796197729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2629847711/5000000000 : ℝ)*x 0 + (2796197709/5000000000 : ℝ)*x 1 + (-105098111/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629847711/5000000000 : ℝ)^2203 ≤ (21649267719059/50000000000000 : ℝ)^1691 := by
    have hnat : (2629847711 : ℕ)^2203*50000000000000^1691 ≤ 21649267719059^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629847711 5000000000 21649267719059 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796197709/5000000000 : ℝ)^2203 ≤ (46900308663551/100000000000000 : ℝ)^1691 := by
    have hnat : (2796197709 : ℕ)^2203*100000000000000^1691 ≤ 46900308663551^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796197709 5000000000 46900308663551 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105098111/625000000 : ℝ)^2203 ≤ (9801155891339/100000000000000 : ℝ)^1691 := by
    have hnat : (105098111 : ℕ)^2203*100000000000000^1691 ≤ 9801155891339^1691*625000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105098111 625000000 9801155891339 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629847711/5000000000 : ℝ), (2796197709/5000000000 : ℝ), (-105098111/625000000 : ℝ)] ![(21649267719059/50000000000000 : ℝ), (46900308663551/100000000000000 : ℝ), (9801155891339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629847711/5000000000 : ℝ)|^2203 ≤ (21649267719059/50000000000000 : ℝ)^1691
        have hw : |(2629847711/5000000000 : ℝ)|=(2629847711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796197709/5000000000 : ℝ)|^2203 ≤ (46900308663551/100000000000000 : ℝ)^1691
        have hw : |(2796197709/5000000000 : ℝ)|=(2796197709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105098111/625000000 : ℝ)|^2203 ≤ (9801155891339/100000000000000 : ℝ)^1691
        have hw : |(-105098111/625000000 : ℝ)|=(105098111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s1_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66786921/156250000 : ℝ)*x 0 + (971366711/2000000000 : ℝ)*x 1 + (1878153311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66786921/156250000 : ℝ)^2203 ≤ (33045083330771/100000000000000 : ℝ)^1691 := by
    have hnat : (66786921 : ℕ)^2203*100000000000000^1691 ≤ 33045083330771^1691*156250000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66786921 156250000 33045083330771 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971366711/2000000000 : ℝ)^2203 ≤ (19514500279539/50000000000000 : ℝ)^1691 := by
    have hnat : (971366711 : ℕ)^2203*50000000000000^1691 ≤ 19514500279539^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971366711 2000000000 19514500279539 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878153311/5000000000 : ℝ)^2203 ≤ (27925916091793/100000000000000 : ℝ)^1691 := by
    have hnat : (1878153311 : ℕ)^2203*100000000000000^1691 ≤ 27925916091793^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878153311 5000000000 27925916091793 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66786921/156250000 : ℝ), (971366711/2000000000 : ℝ), (1878153311/5000000000 : ℝ)] ![(33045083330771/100000000000000 : ℝ), (19514500279539/50000000000000 : ℝ), (27925916091793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66786921/156250000 : ℝ)|^2203 ≤ (33045083330771/100000000000000 : ℝ)^1691
        have hw : |(66786921/156250000 : ℝ)|=(66786921/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(971366711/2000000000 : ℝ)|^2203 ≤ (19514500279539/50000000000000 : ℝ)^1691
        have hw : |(971366711/2000000000 : ℝ)|=(971366711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1878153311/5000000000 : ℝ)|^2203 ≤ (27925916091793/100000000000000 : ℝ)^1691
        have hw : |(1878153311/5000000000 : ℝ)|=(1878153311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (779/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3747/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2167/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (3469269795259/50000000000000000000 : ℝ) := by
    have hpowers : (2167/100000 : ℝ)^4405 ≤ (3469269795259/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2167 : ℕ)^4405*50000000000000000000^1024 ≤ 3469269795259^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2167 100000 3469269795259 50000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2167/100000 : ℝ)) (X := (3469269795259/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26141/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (15575113262484779/5000000000000000000 : ℝ) := by
    have hpowers : (26141/100000 : ℝ)^4405 ≤ (15575113262484779/5000000000000000000 : ℝ)^1024 := by
      have hnat : (26141 : ℕ)^4405*5000000000000000000^1024 ≤ 15575113262484779^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26141 100000 15575113262484779 5000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26141/100000 : ℝ)) (X := (15575113262484779/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003469269795259/25000000000000000000 : ℝ) ≤ (5000000161295441/5000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (25000003469269795259/25000000000000000000 : ℝ)^1024 ≤ (5000000161295441/5000000000000000 : ℝ)^4405 := by
      have hnat : (25000003469269795259 : ℕ)^1024*5000000000000000^4405 ≤ 5000000161295441^4405*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003469269795259 25000000000000000000 5000000161295441 5000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000161295441/5000000000000000 : ℝ)) (X := (25000003469269795259/25000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50155754601894643049/50000000000000000000 : ℝ) ≤ (1250904099841867/1250000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50155754601894643049/50000000000000000000 : ℝ)^1024 ≤ (1250904099841867/1250000000000000 : ℝ)^4405 := by
      have hnat : (50155754601894643049 : ℕ)^1024*1250000000000000^4405 ≤ 1250904099841867^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50155754601894643049 50000000000000000000 1250904099841867 1250000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250904099841867/1250000000000000 : ℝ)) (X := (50155754601894643049/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2515575113262484779/2500000000000000000 : ℝ) ≤ (1001446527487899/1000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (2515575113262484779/2500000000000000000 : ℝ)^1024 ≤ (1001446527487899/1000000000000000 : ℝ)^4405 := by
      have hnat : (2515575113262484779 : ℕ)^1024*1000000000000000^4405 ≤ 1001446527487899^4405*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2515575113262484779 2500000000000000000 1001446527487899 1000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001446527487899/1000000000000000 : ℝ)) (X := (2515575113262484779/2500000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3469269795259/50000000000000000000 : ℝ) ≤ ((29963582772773184379/29967500000000000000 : ℝ)+2*(3616238072027/1198700000000000 : ℝ)*(2167/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (29963582772773184379/29967500000000000000 : ℝ)+2*(3616238072027/1198700000000000 : ℝ)*(2167/100000 : ℝ)=(5000000161295441/5000000000000000 : ℝ) by norm_num, show 1+2*(3469269795259/50000000000000000000 : ℝ)=(25000003469269795259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15575113262484779/5000000000000000000 : ℝ)+(3469269795259/50000000000000000000 : ℝ) ≤ ((29963582772773184379/29967500000000000000 : ℝ)+(3616238072027/1198700000000000 : ℝ)*((26141/100000 : ℝ)+(2167/100000 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (29963582772773184379/29967500000000000000 : ℝ)+(3616238072027/1198700000000000 : ℝ)*((26141/100000 : ℝ)+(2167/100000 : ℝ))=(1250904099841867/1250000000000000 : ℝ) by norm_num, show 1+(15575113262484779/5000000000000000000 : ℝ)+(3469269795259/50000000000000000000 : ℝ)=(50155754601894643049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15575113262484779/5000000000000000000 : ℝ) ≤ ((29963582772773184379/29967500000000000000 : ℝ)+2*(3616238072027/1198700000000000 : ℝ)*(26141/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (29963582772773184379/29967500000000000000 : ℝ)+2*(3616238072027/1198700000000000 : ℝ)*(26141/100000 : ℝ)=(1001446527487899/1000000000000000 : ℝ) by norm_num, show 1+2*(15575113262484779/5000000000000000000 : ℝ)=(2515575113262484779/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29963582772773184379/29967500000000000000 : ℝ)*(X 1 0+X 2 0)+(3616238072027/1198700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (2167/100000 : ℝ)) (hi := (26141/100000 : ℝ)) (c := (29963582772773184379/29967500000000000000 : ℝ)) (alpha := (3616238072027/1198700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29963582772773184379/29967500000000000000 : ℝ)*(X 0 1+X 2 1)+(3616238072027/1198700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (2167/100000 : ℝ)) (hi := (26141/100000 : ℝ)) (c := (29963582772773184379/29967500000000000000 : ℝ)) (alpha := (3616238072027/1198700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29963582772773184379/29967500000000000000 : ℝ)*(X 0 2+X 1 2)+(3616238072027/1198700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (2167/100000 : ℝ)) (hi := (26141/100000 : ℝ)) (c := (29963582772773184379/29967500000000000000 : ℝ)) (alpha := (3616238072027/1198700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1919182559/10000000000 : ℝ)*X 0 0+(279924219/500000000 : ℝ)*X 0 1+(1270209901/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395110683/10000000000 : ℝ)*X 1 0+(-548281399/2500000000 : ℝ)*X 1 1+(158776243/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2697555377/5000000000 : ℝ)*X 2 0+(5080839633/10000000000 : ℝ)*X 2 1+(-2193125687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((534193227/1250000000 : ℝ)*X 0 0+(3743052613/10000000000 : ℝ)*X 0 1+(973973951/2000000000 : ℝ)*X 0 2+(534193227/1250000000 : ℝ)*X 1 0+(3743052613/10000000000 : ℝ)*X 1 1+(973973951/2000000000 : ℝ)*X 1 2+(534193227/1250000000 : ℝ)*X 2 0+(3743052613/10000000000 : ℝ)*X 2 1+(973973951/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-47988949/250000000 : ℝ)*X 0 0+(1271707101/2500000000 : ℝ)*X 0 1+(5592395429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259695509/10000000000 : ℝ)*X 1 0+(-336313919/2000000000 : ℝ)*X 1 1+(2796197729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629847711/5000000000 : ℝ)*X 2 0+(2796197709/5000000000 : ℝ)*X 2 1+(-105098111/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((66786921/156250000 : ℝ)*X 0 0+(971366711/2000000000 : ℝ)*X 0 1+(1878153311/5000000000 : ℝ)*X 0 2+(66786921/156250000 : ℝ)*X 1 0+(971366711/2000000000 : ℝ)*X 1 1+(1878153311/5000000000 : ℝ)*X 1 2+(66786921/156250000 : ℝ)*X 2 0+(971366711/2000000000 : ℝ)*X 2 1+(1878153311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4506252010089527304987133521/749187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48247039/100000000000000 : ℝ)*(base1) + (1078267427/100000000000000 : ℝ)*(base19) + (137961323/12500000000000 : ℝ)*(base23) + (70832547/50000000000000 : ℝ)*(upper3) + (104941863/100000000000000 : ℝ)*(upper5) + (704826266667511/50000000000000 : ℝ)*(major0) + (704826266667511/50000000000000 : ℝ)*(major1) + (704826266667511/50000000000000 : ℝ)*(major2) + (965917353494969/50000000000000 : ℝ)*(sp0) + (965920675112593/50000000000000 : ℝ)*(sp1) + (193184132480203/10000000000000 : ℝ)*(sp2) + (887458761577809/100000000000000 : ℝ)*(sp3) + (3884874857/50000000000000 : ℝ)*(sp4) + (3627857507/100000000000000 : ℝ)*(sp7) + (177492487536471/20000000000000 : ℝ)*(f.failure) + (1931842428492613/100000000000000 : ℝ)*(f.sum) + (27007510469339/14983750000000000000000000000 : ℝ)*base66 + (9784100171291314331/1498375000000000000000000000000000 : ℝ)*base68 + (1657937275226689331/1498375000000000000000000000000000 : ℝ)*base70 + (13260813535079314331/1498375000000000000000000000000000 : ℝ)*base72 + (17342199111651/3745937500000000000000000000 : ℝ)*base74 + (7528924857949939331/1498375000000000000000000000000000 : ℝ)*base76 + (3565980534133564331/1498375000000000000000000000000000 : ℝ)*base78 + (21840939570888564331/1498375000000000000000000000000000 : ℝ)*base80 + (69789277469629/59935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5717981/2000000000000000000000 : ℝ)*base89 + (5717981/2000000000000000000000 : ℝ)*base91 + (5717981/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3144227868873888218000583861/299675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21670619/25000000000000 : ℝ)*(base1) + (13765053/625000000000 : ℝ)*(base19) + (539568949/25000000000000 : ℝ)*(base23) + (254924977/100000000000000 : ℝ)*(upper3) + (220776257/100000000000000 : ℝ)*(upper5) + (288663263034853/20000000000000 : ℝ)*(major0) + (288663263034853/20000000000000 : ℝ)*(major1) + (288663263034853/20000000000000 : ℝ)*(major2) + (205582901/1562500000000 : ℝ)*(sp1) + (12713908277/100000000000000 : ℝ)*(sp2) + (988988260587253/50000000000000 : ℝ)*(sp4) + (1977961074777887/100000000000000 : ℝ)*(sp5) + (988980781153979/50000000000000 : ℝ)*(sp6) + (454327879718241/50000000000000 : ℝ)*(sp7) + (454327923059479/50000000000000 : ℝ)*(f.failure) + (197797643449203/10000000000000 : ℝ)*(f.sum) + (1142700520149/2397400000000000000000000000 : ℝ)*base66 + (285044854744963713/599350000000000000000000000000000 : ℝ)*base68 + (2044931300568636287/599350000000000000000000000000000 : ℝ)*base69 + (2620843103750113713/599350000000000000000000000000000 : ℝ)*base72 + (10690850690261/2996750000000000000000000000 : ℝ)*base73 + (8259810383997963713/599350000000000000000000000000000 : ℝ)*base76 + (2000228622590236287/599350000000000000000000000000000 : ℝ)*base77 + (9497659914610313713/599350000000000000000000000000000 : ℝ)*base80 + (18181937257323/2996750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4402531/5000000000000000000000 : ℝ)*base90 + (4402531/5000000000000000000000 : ℝ)*base92 + (4402531/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1446_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (779/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3747/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1446_s2_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-390212687/2000000000 : ℝ)*x 0 + (5454442811/10000000000 : ℝ)*x 1 + (1301085247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390212687/2000000000 : ℝ)^2203 ≤ (5947715368583/50000000000000 : ℝ)^1691 := by
    have hnat : (390212687 : ℕ)^2203*50000000000000^1691 ≤ 5947715368583^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390212687 2000000000 5947715368583 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454442811/10000000000 : ℝ)^2203 ≤ (45398743079017/100000000000000 : ℝ)^1691 := by
    have hnat : (5454442811 : ℕ)^2203*100000000000000^1691 ≤ 45398743079017^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454442811 10000000000 45398743079017 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301085247/2500000000 : ℝ)^2203 ≤ (42705826176009/100000000000000 : ℝ)^1691 := by
    have hnat : (1301085247 : ℕ)^2203*100000000000000^1691 ≤ 42705826176009^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301085247 2500000000 42705826176009 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390212687/2000000000 : ℝ), (5454442811/10000000000 : ℝ), (1301085247/2500000000 : ℝ)] ![(5947715368583/50000000000000 : ℝ), (45398743079017/100000000000000 : ℝ), (42705826176009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390212687/2000000000 : ℝ)|^2203 ≤ (5947715368583/50000000000000 : ℝ)^1691
        have hw : |(-390212687/2000000000 : ℝ)|=(390212687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454442811/10000000000 : ℝ)|^2203 ≤ (45398743079017/100000000000000 : ℝ)^1691
        have hw : |(5454442811/10000000000 : ℝ)|=(5454442811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301085247/2500000000 : ℝ)|^2203 ≤ (42705826176009/100000000000000 : ℝ)^1691
        have hw : |(1301085247/2500000000 : ℝ)|=(1301085247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5359075787/10000000000 : ℝ)*x 0 + (-2079645637/10000000000 : ℝ)*x 1 + (5204340683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359075787/10000000000 : ℝ)^2203 ≤ (22183695721427/50000000000000 : ℝ)^1691 := by
    have hnat : (5359075787 : ℕ)^2203*50000000000000^1691 ≤ 22183695721427^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359075787 10000000000 22183695721427 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079645637/10000000000 : ℝ)^2203 ≤ (807924101683/6250000000000 : ℝ)^1691 := by
    have hnat : (2079645637 : ℕ)^2203*6250000000000^1691 ≤ 807924101683^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079645637 10000000000 807924101683 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204340683/10000000000 : ℝ)^2203 ≤ (854116458309/2000000000000 : ℝ)^1691 := by
    have hnat : (5204340683 : ℕ)^2203*2000000000000^1691 ≤ 854116458309^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204340683 10000000000 854116458309 2000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359075787/10000000000 : ℝ), (-2079645637/10000000000 : ℝ), (5204340683/10000000000 : ℝ)] ![(22183695721427/50000000000000 : ℝ), (807924101683/6250000000000 : ℝ), (854116458309/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359075787/10000000000 : ℝ)|^2203 ≤ (22183695721427/50000000000000 : ℝ)^1691
        have hw : |(5359075787/10000000000 : ℝ)|=(5359075787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079645637/10000000000 : ℝ)|^2203 ≤ (807924101683/6250000000000 : ℝ)^1691
        have hw : |(-2079645637/10000000000 : ℝ)|=(2079645637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204340683/10000000000 : ℝ)|^2203 ≤ (854116458309/2000000000000 : ℝ)^1691
        have hw : |(5204340683/10000000000 : ℝ)|=(5204340683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5359075191/10000000000 : ℝ)*x 0 + (2602170627/5000000000 : ℝ)*x 1 + (-2079645677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359075191/10000000000 : ℝ)^2203 ≤ (11091846253657/25000000000000 : ℝ)^1691 := by
    have hnat : (5359075191 : ℕ)^2203*25000000000000^1691 ≤ 11091846253657^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359075191 10000000000 11091846253657 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602170627/5000000000 : ℝ)^2203 ≤ (10676457254911/25000000000000 : ℝ)^1691 := by
    have hnat : (2602170627 : ℕ)^2203*25000000000000^1691 ≤ 10676457254911^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602170627 5000000000 10676457254911 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079645677/10000000000 : ℝ)^2203 ≤ (3231696487711/25000000000000 : ℝ)^1691 := by
    have hnat : (2079645677 : ℕ)^2203*25000000000000^1691 ≤ 3231696487711^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079645677 10000000000 3231696487711 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359075191/10000000000 : ℝ), (2602170627/5000000000 : ℝ), (-2079645677/10000000000 : ℝ)] ![(11091846253657/25000000000000 : ℝ), (10676457254911/25000000000000 : ℝ), (3231696487711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359075191/10000000000 : ℝ)|^2203 ≤ (11091846253657/25000000000000 : ℝ)^1691
        have hw : |(5359075191/10000000000 : ℝ)|=(5359075191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602170627/5000000000 : ℝ)|^2203 ≤ (10676457254911/25000000000000 : ℝ)^1691
        have hw : |(2602170627/5000000000 : ℝ)|=(2602170627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079645677/10000000000 : ℝ)|^2203 ≤ (3231696487711/25000000000000 : ℝ)^1691
        have hw : |(-2079645677/10000000000 : ℝ)|=(2079645677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074022701/2500000000 : ℝ)*x 0 + (806312579/2000000000 : ℝ)*x 1 + (4575989929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074022701/2500000000 : ℝ)^2203 ≤ (6652817964887/20000000000000 : ℝ)^1691 := by
    have hnat : (1074022701 : ℕ)^2203*20000000000000^1691 ≤ 6652817964887^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074022701 2500000000 6652817964887 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806312579/2000000000 : ℝ)^2203 ≤ (30620968033209/100000000000000 : ℝ)^1691 := by
    have hnat : (806312579 : ℕ)^2203*100000000000000^1691 ≤ 30620968033209^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806312579 2000000000 30620968033209 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4575989929/10000000000 : ℝ)^2203 ≤ (18057471061109/50000000000000 : ℝ)^1691 := by
    have hnat : (4575989929 : ℕ)^2203*50000000000000^1691 ≤ 18057471061109^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575989929 10000000000 18057471061109 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074022701/2500000000 : ℝ), (806312579/2000000000 : ℝ), (4575989929/10000000000 : ℝ)] ![(6652817964887/20000000000000 : ℝ), (30620968033209/100000000000000 : ℝ), (18057471061109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074022701/2500000000 : ℝ)|^2203 ≤ (6652817964887/20000000000000 : ℝ)^1691
        have hw : |(1074022701/2500000000 : ℝ)|=(1074022701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806312579/2000000000 : ℝ)|^2203 ≤ (30620968033209/100000000000000 : ℝ)^1691
        have hw : |(806312579/2000000000 : ℝ)|=(806312579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4575989929/10000000000 : ℝ)|^2203 ≤ (18057471061109/50000000000000 : ℝ)^1691
        have hw : |(4575989929/10000000000 : ℝ)|=(4575989929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951105543/10000000000 : ℝ)*x 0 + (5205748501/10000000000 : ℝ)*x 1 + (2726512101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951105543/10000000000 : ℝ)^2203 ≤ (11895765198337/100000000000000 : ℝ)^1691 := by
    have hnat : (1951105543 : ℕ)^2203*100000000000000^1691 ≤ 11895765198337^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951105543 10000000000 11895765198337 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205748501/10000000000 : ℝ)^2203 ≤ (42720873610751/100000000000000 : ℝ)^1691 := by
    have hnat : (5205748501 : ℕ)^2203*100000000000000^1691 ≤ 42720873610751^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205748501 10000000000 42720873610751 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726512101/5000000000 : ℝ)^2203 ≤ (567292014759/1250000000000 : ℝ)^1691 := by
    have hnat : (2726512101 : ℕ)^2203*1250000000000^1691 ≤ 567292014759^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726512101 5000000000 567292014759 1250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951105543/10000000000 : ℝ), (5205748501/10000000000 : ℝ), (2726512101/5000000000 : ℝ)] ![(11895765198337/100000000000000 : ℝ), (42720873610751/100000000000000 : ℝ), (567292014759/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951105543/10000000000 : ℝ)|^2203 ≤ (11895765198337/100000000000000 : ℝ)^1691
        have hw : |(-1951105543/10000000000 : ℝ)|=(1951105543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205748501/10000000000 : ℝ)|^2203 ≤ (42720873610751/100000000000000 : ℝ)^1691
        have hw : |(5205748501/10000000000 : ℝ)|=(5205748501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726512101/5000000000 : ℝ)|^2203 ≤ (567292014759/1250000000000 : ℝ)^1691
        have hw : |(2726512101/5000000000 : ℝ)|=(2726512101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (661742269/1250000000 : ℝ)*x 0 + (-1830960811/10000000000 : ℝ)*x 1 + (2726512711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661742269/1250000000 : ℝ)^2203 ≤ (10916534614387/25000000000000 : ℝ)^1691 := by
    have hnat : (661742269 : ℕ)^2203*25000000000000^1691 ≤ 10916534614387^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661742269 1250000000 10916534614387 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830960811/10000000000 : ℝ)^2203 ≤ (10950487120569/100000000000000 : ℝ)^1691 := by
    have hnat : (1830960811 : ℕ)^2203*100000000000000^1691 ≤ 10950487120569^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830960811 10000000000 10950487120569 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726512711/5000000000 : ℝ)^2203 ≤ (2836460900537/6250000000000 : ℝ)^1691 := by
    have hnat : (2726512711 : ℕ)^2203*6250000000000^1691 ≤ 2836460900537^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726512711 5000000000 2836460900537 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661742269/1250000000 : ℝ), (-1830960811/10000000000 : ℝ), (2726512711/5000000000 : ℝ)] ![(10916534614387/25000000000000 : ℝ), (10950487120569/100000000000000 : ℝ), (2836460900537/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661742269/1250000000 : ℝ)|^2203 ≤ (10916534614387/25000000000000 : ℝ)^1691
        have hw : |(661742269/1250000000 : ℝ)|=(661742269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1830960811/10000000000 : ℝ)|^2203 ≤ (10950487120569/100000000000000 : ℝ)^1691
        have hw : |(-1830960811/10000000000 : ℝ)|=(1830960811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726512711/5000000000 : ℝ)|^2203 ≤ (2836460900537/6250000000000 : ℝ)^1691
        have hw : |(2726512711/5000000000 : ℝ)|=(2726512711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1323484331/2500000000 : ℝ)*x 0 + (5453025151/10000000000 : ℝ)*x 1 + (-1830962329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323484331/2500000000 : ℝ)^2203 ≤ (21833064780033/50000000000000 : ℝ)^1691 := by
    have hnat : (1323484331 : ℕ)^2203*50000000000000^1691 ≤ 21833064780033^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323484331 2500000000 21833064780033 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453025151/10000000000 : ℝ)^2203 ≤ (45383371470269/100000000000000 : ℝ)^1691 := by
    have hnat : (5453025151 : ℕ)^2203*100000000000000^1691 ≤ 45383371470269^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453025151 10000000000 45383371470269 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1830962329/10000000000 : ℝ)^2203 ≤ (5475249474091/50000000000000 : ℝ)^1691 := by
    have hnat : (1830962329 : ℕ)^2203*50000000000000^1691 ≤ 5475249474091^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830962329 10000000000 5475249474091 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323484331/2500000000 : ℝ), (5453025151/10000000000 : ℝ), (-1830962329/10000000000 : ℝ)] ![(21833064780033/50000000000000 : ℝ), (45383371470269/100000000000000 : ℝ), (5475249474091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323484331/2500000000 : ℝ)|^2203 ≤ (21833064780033/50000000000000 : ℝ)^1691
        have hw : |(1323484331/2500000000 : ℝ)|=(1323484331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453025151/10000000000 : ℝ)|^2203 ≤ (45383371470269/100000000000000 : ℝ)^1691
        have hw : |(5453025151/10000000000 : ℝ)|=(5453025151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1830962329/10000000000 : ℝ)|^2203 ≤ (5475249474091/50000000000000 : ℝ)^1691
        have hw : |(-1830962329/10000000000 : ℝ)|=(1830962329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s2_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074045787/2500000000 : ℝ)*x 0 + (71451997/156250000 : ℝ)*x 1 + (4034649919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074045787/2500000000 : ℝ)^2203 ≤ (33265021325119/100000000000000 : ℝ)^1691 := by
    have hnat : (1074045787 : ℕ)^2203*100000000000000^1691 ≤ 33265021325119^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074045787 2500000000 33265021325119 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71451997/156250000 : ℝ)^2203 ≤ (36083460935507/100000000000000 : ℝ)^1691 := by
    have hnat : (71451997 : ℕ)^2203*100000000000000^1691 ≤ 36083460935507^1691*156250000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71451997 156250000 36083460935507 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034649919/10000000000 : ℝ)^2203 ≤ (30651517715931/100000000000000 : ℝ)^1691 := by
    have hnat : (4034649919 : ℕ)^2203*100000000000000^1691 ≤ 30651517715931^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034649919 10000000000 30651517715931 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074045787/2500000000 : ℝ), (71451997/156250000 : ℝ), (4034649919/10000000000 : ℝ)] ![(33265021325119/100000000000000 : ℝ), (36083460935507/100000000000000 : ℝ), (30651517715931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074045787/2500000000 : ℝ)|^2203 ≤ (33265021325119/100000000000000 : ℝ)^1691
        have hw : |(1074045787/2500000000 : ℝ)|=(1074045787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71451997/156250000 : ℝ)|^2203 ≤ (36083460935507/100000000000000 : ℝ)^1691
        have hw : |(71451997/156250000 : ℝ)|=(71451997/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034649919/10000000000 : ℝ)|^2203 ≤ (30651517715931/100000000000000 : ℝ)^1691
        have hw : |(4034649919/10000000000 : ℝ)|=(4034649919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3747/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (779/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1307/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3747/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (779/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3747/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (779/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3747/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (779/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3747/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (779/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3747/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (779/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3747/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (779/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (779/10000 : ℝ) ^ (4405/1024 : ℝ) ≤ (213094682053791/12500000000000000000 : ℝ) := by
    have hpowers : (779/10000 : ℝ)^4405 ≤ (213094682053791/12500000000000000000 : ℝ)^1024 := by
      have hnat : (779 : ℕ)^4405*12500000000000000000^1024 ≤ 213094682053791^1024*10000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        779 10000 213094682053791 12500000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (779/10000 : ℝ)) (X := (213094682053791/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3747/20000 : ℝ) ^ (4405/1024 : ℝ) ≤ (74324562337123897/100000000000000000000 : ℝ) := by
    have hpowers : (3747/20000 : ℝ)^4405 ≤ (74324562337123897/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3747 : ℕ)^4405*100000000000000000000^1024 ≤ 74324562337123897^1024*20000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3747 20000 74324562337123897 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3747/20000 : ℝ)) (X := (74324562337123897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250213094682053791/6250000000000000000 : ℝ) ≤ (10000079257607009/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (6250213094682053791/6250000000000000000 : ℝ)^1024 ≤ (10000079257607009/10000000000000000 : ℝ)^4405 := by
      have hnat : (6250213094682053791 : ℕ)^1024*10000000000000000^4405 ≤ 10000079257607009^4405*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250213094682053791 6250000000000000000 10000079257607009 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000079257607009/10000000000000000 : ℝ)) (X := (6250213094682053791/6250000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4003041172791742169/4000000000000000000 : ℝ) ≤ (1250220860719811/1250000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (4003041172791742169/4000000000000000000 : ℝ)^1024 ≤ (1250220860719811/1250000000000000 : ℝ)^4405 := by
      have hnat : (4003041172791742169 : ℕ)^1024*1250000000000000^4405 ≤ 1250220860719811^4405*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003041172791742169 4000000000000000000 1250220860719811 1250000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250220860719811/1250000000000000 : ℝ)) (X := (4003041172791742169/4000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50074324562337123897/50000000000000000000 : ℝ) ≤ (10003454513909967/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50074324562337123897/50000000000000000000 : ℝ)^1024 ≤ (10003454513909967/10000000000000000 : ℝ)^4405 := by
      have hnat : (50074324562337123897 : ℕ)^1024*10000000000000000^4405 ≤ 10003454513909967^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074324562337123897 50000000000000000000 10003454513909967 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003454513909967/10000000000000000 : ℝ)) (X := (50074324562337123897/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(213094682053791/12500000000000000000 : ℝ) ≤ ((21884914845581734137/21890000000000000000 : ℝ)+2*(1687628151479/1094500000000000 : ℝ)*(779/10000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (21884914845581734137/21890000000000000000 : ℝ)+2*(1687628151479/1094500000000000 : ℝ)*(779/10000 : ℝ)=(10000079257607009/10000000000000000 : ℝ) by norm_num, show 1+2*(213094682053791/12500000000000000000 : ℝ)=(6250213094682053791/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74324562337123897/100000000000000000000 : ℝ)+(213094682053791/12500000000000000000 : ℝ) ≤ ((21884914845581734137/21890000000000000000 : ℝ)+(1687628151479/1094500000000000 : ℝ)*((3747/20000 : ℝ)+(779/10000 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (21884914845581734137/21890000000000000000 : ℝ)+(1687628151479/1094500000000000 : ℝ)*((3747/20000 : ℝ)+(779/10000 : ℝ))=(1250220860719811/1250000000000000 : ℝ) by norm_num, show 1+(74324562337123897/100000000000000000000 : ℝ)+(213094682053791/12500000000000000000 : ℝ)=(4003041172791742169/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74324562337123897/100000000000000000000 : ℝ) ≤ ((21884914845581734137/21890000000000000000 : ℝ)+2*(1687628151479/1094500000000000 : ℝ)*(3747/20000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (21884914845581734137/21890000000000000000 : ℝ)+2*(1687628151479/1094500000000000 : ℝ)*(3747/20000 : ℝ)=(10003454513909967/10000000000000000 : ℝ) by norm_num, show 1+2*(74324562337123897/100000000000000000000 : ℝ)=(50074324562337123897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21884914845581734137/21890000000000000000 : ℝ)*(X 1 0+X 2 0)+(1687628151479/1094500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (779/10000 : ℝ)) (hi := (3747/20000 : ℝ)) (c := (21884914845581734137/21890000000000000000 : ℝ)) (alpha := (1687628151479/1094500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21884914845581734137/21890000000000000000 : ℝ)*(X 0 1+X 2 1)+(1687628151479/1094500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (779/10000 : ℝ)) (hi := (3747/20000 : ℝ)) (c := (21884914845581734137/21890000000000000000 : ℝ)) (alpha := (1687628151479/1094500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21884914845581734137/21890000000000000000 : ℝ)*(X 0 2+X 1 2)+(1687628151479/1094500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (779/10000 : ℝ)) (hi := (3747/20000 : ℝ)) (c := (21884914845581734137/21890000000000000000 : ℝ)) (alpha := (1687628151479/1094500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-390212687/2000000000 : ℝ)*X 0 0+(5454442811/10000000000 : ℝ)*X 0 1+(1301085247/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359075787/10000000000 : ℝ)*X 1 0+(-2079645637/10000000000 : ℝ)*X 1 1+(5204340683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5359075191/10000000000 : ℝ)*X 2 0+(2602170627/5000000000 : ℝ)*X 2 1+(-2079645677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074022701/2500000000 : ℝ)*X 0 0+(806312579/2000000000 : ℝ)*X 0 1+(4575989929/10000000000 : ℝ)*X 0 2+(1074022701/2500000000 : ℝ)*X 1 0+(806312579/2000000000 : ℝ)*X 1 1+(4575989929/10000000000 : ℝ)*X 1 2+(1074022701/2500000000 : ℝ)*X 2 0+(806312579/2000000000 : ℝ)*X 2 1+(4575989929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1951105543/10000000000 : ℝ)*X 0 0+(5205748501/10000000000 : ℝ)*X 0 1+(2726512101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661742269/1250000000 : ℝ)*X 1 0+(-1830960811/10000000000 : ℝ)*X 1 1+(2726512711/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323484331/2500000000 : ℝ)*X 2 0+(5453025151/10000000000 : ℝ)*X 2 1+(-1830962329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074045787/2500000000 : ℝ)*X 0 0+(71451997/156250000 : ℝ)*X 0 1+(4034649919/10000000000 : ℝ)*X 0 2+(1074045787/2500000000 : ℝ)*X 1 0+(71451997/156250000 : ℝ)*X 1 1+(4034649919/10000000000 : ℝ)*X 1 2+(1074045787/2500000000 : ℝ)*X 2 0+(71451997/156250000 : ℝ)*X 2 1+(4034649919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6361780434185131406053703181/547250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26798301/1562500000000 : ℝ)*(base19) + (495514739/50000000000000 : ℝ)*(base23) + (149725377/100000000000000 : ℝ)*(lower2) + (402549533/100000000000000 : ℝ)*(upper3) + (65583127/100000000000000 : ℝ)*(upper5) + (1458804369367929/50000000000000 : ℝ)*(major0) + (1458804369367929/50000000000000 : ℝ)*(major1) + (1458804369367929/50000000000000 : ℝ)*(major2) + (1999196030484509/50000000000000 : ℝ)*(sp0) + (1999201164466799/50000000000000 : ℝ)*(sp1) + (499800381624423/12500000000000 : ℝ)*(sp2) + (1836801609263533/100000000000000 : ℝ)*(sp3) + (2995763961/25000000000000 : ℝ)*(sp4) + (5718341683/50000000000000 : ℝ)*(sp7) + (18368130459469/1000000000000 : ℝ)*(f.failure) + (1999202022012431/50000000000000 : ℝ)*(f.sum) + (32880316986767/13681250000000000000000000000 : ℝ)*base66 + (2347693971879612273/1094500000000000000000000000000000 : ℝ)*base67 + (1099325245758612273/1094500000000000000000000000000000 : ℝ)*base69 + (390842571054887727/1094500000000000000000000000000000 : ℝ)*base72 + (16889032404157/54725000000000000000000000000 : ℝ)*base73 + (6077197533949612273/1094500000000000000000000000000000 : ℝ)*base75 + (3922224336094112273/1094500000000000000000000000000000 : ℝ)*base77 + (2026641745003387727/1094500000000000000000000000000000 : ℝ)*base80 + (208945669843307/54725000000000000000000000000 : ℝ)*base81 + (589359/100000000000000000000 : ℝ)*base89 + (589359/100000000000000000000 : ℝ)*base91 + (589359/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (301170462192899695547637339/27362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123215873/20000000000000 : ℝ)*(base19) + (160373373/50000000000000 : ℝ)*(base23) + (128877647/50000000000000 : ℝ)*(upper3) + (533739/195312500000 : ℝ)*(lower4) + (73772976409749/2500000000000 : ℝ)*(major0) + (73772976409749/2500000000000 : ℝ)*(major1) + (73772976409749/2500000000000 : ℝ)*(major2) + (20739068857/100000000000000 : ℝ)*(sp1) + (3094620017/50000000000000 : ℝ)*(sp2) + (2075456879/50000000000000 : ℝ)*(sp3) + (1011013454704409/25000000000000 : ℝ)*(sp4) + (2022016231834707/50000000000000 : ℝ)*(sp5) + (2022023654415427/50000000000000 : ℝ)*(sp6) + (464444944039741/25000000000000 : ℝ)*(sp7) + (928891963536361/50000000000000 : ℝ)*(f.failure) + (1011013454704409/25000000000000 : ℝ)*(f.sum) + (8193346964813/2736250000000000000000000000 : ℝ)*base66 + (492934611533228387/54725000000000000000000000000000 : ℝ)*base68 + (487541441549928387/54725000000000000000000000000000 : ℝ)*base70 + (411893701601653387/54725000000000000000000000000000 : ℝ)*base72 + (1540775227413/10945000000000000000000000000 : ℝ)*base73 + (697511720704003387/54725000000000000000000000000000 : ℝ)*base76 + (191053061004171613/54725000000000000000000000000000 : ℝ)*base77 + (770008503184121613/54725000000000000000000000000000 : ℝ)*base79 + (25787744936281/5472500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (9228771/5000000000000000000000 : ℝ)*base89 + (9228771/5000000000000000000000 : ℝ)*base91 + (9228771/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1446_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3747/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (779/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1446_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1446_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1446_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1446_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

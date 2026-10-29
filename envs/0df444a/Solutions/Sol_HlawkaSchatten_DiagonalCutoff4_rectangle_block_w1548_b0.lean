-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1548_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:25.348872+00:00
-- url     : https://prove2.me/submissions/85dd58cc-f351-4a30-9696-fb26802dc0f0

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
theorem support_rectangle_w1548_s0_0 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-824154537/5000000000 : ℝ)*x 0 + (5885643537/10000000000 : ℝ)*x 1 + (2435208401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824154537/5000000000 : ℝ)^4593 ≤ (9826417526937/100000000000000 : ℝ)^3569 := by
    have hnat : (824154537 : ℕ)^4593*100000000000000^3569 ≤ 9826417526937^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824154537 5000000000 9826417526937 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5885643537/10000000000 : ℝ)^4593 ≤ (3159543813787/6250000000000 : ℝ)^3569 := by
    have hnat : (5885643537 : ℕ)^4593*6250000000000^3569 ≤ 3159543813787^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5885643537 10000000000 3159543813787 6250000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2435208401/5000000000 : ℝ)^4593 ≤ (39620881434487/100000000000000 : ℝ)^3569 := by
    have hnat : (2435208401 : ℕ)^4593*100000000000000^3569 ≤ 39620881434487^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435208401 5000000000 39620881434487 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-824154537/5000000000 : ℝ), (5885643537/10000000000 : ℝ), (2435208401/5000000000 : ℝ)] ![(9826417526937/100000000000000 : ℝ), (3159543813787/6250000000000 : ℝ), (39620881434487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-824154537/5000000000 : ℝ)|^4593 ≤ (9826417526937/100000000000000 : ℝ)^3569
        have hw : |(-824154537/5000000000 : ℝ)|=(824154537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5885643537/10000000000 : ℝ)|^4593 ≤ (3159543813787/6250000000000 : ℝ)^3569
        have hw : |(5885643537/10000000000 : ℝ)|=(5885643537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2435208401/5000000000 : ℝ)|^4593 ≤ (39620881434487/100000000000000 : ℝ)^3569
        have hw : |(2435208401/5000000000 : ℝ)|=(2435208401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_1 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341886927/625000000 : ℝ)*x 0 + (-2214782683/10000000000 : ℝ)*x 1 + (4870416799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341886927/625000000 : ℝ)^4593 ≤ (46007796251459/100000000000000 : ℝ)^3569 := by
    have hnat : (341886927 : ℕ)^4593*100000000000000^3569 ≤ 46007796251459^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341886927 625000000 46007796251459 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214782683/10000000000 : ℝ)^4593 ≤ (14371322334461/100000000000000 : ℝ)^3569 := by
    have hnat : (2214782683 : ℕ)^4593*100000000000000^3569 ≤ 14371322334461^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214782683 10000000000 14371322334461 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4870416799/10000000000 : ℝ)^4593 ≤ (990522035077/2500000000000 : ℝ)^3569 := by
    have hnat : (4870416799 : ℕ)^4593*2500000000000^3569 ≤ 990522035077^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870416799 10000000000 990522035077 2500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341886927/625000000 : ℝ), (-2214782683/10000000000 : ℝ), (4870416799/10000000000 : ℝ)] ![(46007796251459/100000000000000 : ℝ), (14371322334461/100000000000000 : ℝ), (990522035077/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341886927/625000000 : ℝ)|^4593 ≤ (46007796251459/100000000000000 : ℝ)^3569
        have hw : |(341886927/625000000 : ℝ)|=(341886927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214782683/10000000000 : ℝ)|^4593 ≤ (14371322334461/100000000000000 : ℝ)^3569
        have hw : |(-2214782683/10000000000 : ℝ)|=(2214782683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4870416799/10000000000 : ℝ)|^4593 ≤ (990522035077/2500000000000 : ℝ)^3569
        have hw : |(4870416799/10000000000 : ℝ)|=(4870416799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_2 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341886929/625000000 : ℝ)*x 0 + (4870416761/10000000000 : ℝ)*x 1 + (-69211959/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341886929/625000000 : ℝ)^4593 ≤ (2300389829891/5000000000000 : ℝ)^3569 := by
    have hnat : (341886929 : ℕ)^4593*5000000000000^3569 ≤ 2300389829891^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341886929 625000000 2300389829891 5000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870416761/10000000000 : ℝ)^4593 ≤ (7924176201051/20000000000000 : ℝ)^3569 := by
    have hnat : (4870416761 : ℕ)^4593*20000000000000^3569 ≤ 7924176201051^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870416761 10000000000 7924176201051 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69211959/312500000 : ℝ)^4593 ≤ (7185661188107/50000000000000 : ℝ)^3569 := by
    have hnat : (69211959 : ℕ)^4593*50000000000000^3569 ≤ 7185661188107^3569*312500000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69211959 312500000 7185661188107 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341886929/625000000 : ℝ), (4870416761/10000000000 : ℝ), (-69211959/312500000 : ℝ)] ![(2300389829891/5000000000000 : ℝ), (7924176201051/20000000000000 : ℝ), (7185661188107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341886929/625000000 : ℝ)|^4593 ≤ (2300389829891/5000000000000 : ℝ)^3569
        have hw : |(341886929/625000000 : ℝ)|=(341886929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4870416761/10000000000 : ℝ)|^4593 ≤ (7924176201051/20000000000000 : ℝ)^3569
        have hw : |(4870416761/10000000000 : ℝ)|=(4870416761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69211959/312500000 : ℝ)|^4593 ≤ (7185661188107/50000000000000 : ℝ)^3569
        have hw : |(-69211959/312500000 : ℝ)|=(69211959/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_3 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135572823/10000000000 : ℝ)*x 0 + (193257543/625000000 : ℝ)*x 1 + (272637579/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135572823/10000000000 : ℝ)^4593 ≤ (32100660315543/100000000000000 : ℝ)^3569 := by
    have hnat : (4135572823 : ℕ)^4593*100000000000000^3569 ≤ 32100660315543^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135572823 10000000000 32100660315543 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193257543/625000000 : ℝ)^4593 ≤ (22080215603859/100000000000000 : ℝ)^3569 := by
    have hnat : (193257543 : ℕ)^4593*100000000000000^3569 ≤ 22080215603859^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193257543 625000000 22080215603859 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272637579/500000000 : ℝ)^4593 ≤ (45819124064319/100000000000000 : ℝ)^3569 := by
    have hnat : (272637579 : ℕ)^4593*100000000000000^3569 ≤ 45819124064319^3569*500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272637579 500000000 45819124064319 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135572823/10000000000 : ℝ), (193257543/625000000 : ℝ), (272637579/500000000 : ℝ)] ![(32100660315543/100000000000000 : ℝ), (22080215603859/100000000000000 : ℝ), (45819124064319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135572823/10000000000 : ℝ)|^4593 ≤ (32100660315543/100000000000000 : ℝ)^3569
        have hw : |(4135572823/10000000000 : ℝ)|=(4135572823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193257543/625000000 : ℝ)|^4593 ≤ (22080215603859/100000000000000 : ℝ)^3569
        have hw : |(193257543/625000000 : ℝ)|=(193257543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272637579/500000000 : ℝ)|^4593 ≤ (45819124064319/100000000000000 : ℝ)^3569
        have hw : |(272637579/500000000 : ℝ)|=(272637579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_4 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41288357/250000000 : ℝ)*x 0 + (306007817/625000000 : ℝ)*x 1 + (5859019703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41288357/250000000 : ℝ)^4593 ≤ (615698008011/6250000000000 : ℝ)^3569 := by
    have hnat : (41288357 : ℕ)^4593*6250000000000^3569 ≤ 615698008011^3569*250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41288357 250000000 615698008011 6250000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306007817/625000000 : ℝ)^4593 ≤ (319121812283/800000000000 : ℝ)^3569 := by
    have hnat : (306007817 : ℕ)^4593*800000000000^3569 ≤ 319121812283^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306007817 625000000 319121812283 800000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5859019703/10000000000 : ℝ)^4593 ≤ (50258605316979/100000000000000 : ℝ)^3569 := by
    have hnat : (5859019703 : ℕ)^4593*100000000000000^3569 ≤ 50258605316979^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5859019703 10000000000 50258605316979 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41288357/250000000 : ℝ), (306007817/625000000 : ℝ), (5859019703/10000000000 : ℝ)] ![(615698008011/6250000000000 : ℝ), (319121812283/800000000000 : ℝ), (50258605316979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41288357/250000000 : ℝ)|^4593 ≤ (615698008011/6250000000000 : ℝ)^3569
        have hw : |(-41288357/250000000 : ℝ)|=(41288357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(306007817/625000000 : ℝ)|^4593 ≤ (319121812283/800000000000 : ℝ)^3569
        have hw : |(306007817/625000000 : ℝ)|=(306007817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5859019703/10000000000 : ℝ)|^4593 ≤ (50258605316979/100000000000000 : ℝ)^3569
        have hw : |(5859019703/10000000000 : ℝ)|=(5859019703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_5 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649087067/1250000000 : ℝ)*x 0 + (-613090111/5000000000 : ℝ)*x 1 + (5859019331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649087067/1250000000 : ℝ)^4593 ≤ (672287298253/1562500000000 : ℝ)^3569 := by
    have hnat : (649087067 : ℕ)^4593*1562500000000^3569 ≤ 672287298253^3569*1250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649087067 1250000000 672287298253 1562500000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613090111/5000000000 : ℝ)^4593 ≤ (6715011681307/100000000000000 : ℝ)^3569 := by
    have hnat : (613090111 : ℕ)^4593*100000000000000^3569 ≤ 6715011681307^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613090111 5000000000 6715011681307 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5859019331/10000000000 : ℝ)^4593 ≤ (50258601210417/100000000000000 : ℝ)^3569 := by
    have hnat : (5859019331 : ℕ)^4593*100000000000000^3569 ≤ 50258601210417^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5859019331 10000000000 50258601210417 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649087067/1250000000 : ℝ), (-613090111/5000000000 : ℝ), (5859019331/10000000000 : ℝ)] ![(672287298253/1562500000000 : ℝ), (6715011681307/100000000000000 : ℝ), (50258601210417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649087067/1250000000 : ℝ)|^4593 ≤ (672287298253/1562500000000 : ℝ)^3569
        have hw : |(649087067/1250000000 : ℝ)|=(649087067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-613090111/5000000000 : ℝ)|^4593 ≤ (6715011681307/100000000000000 : ℝ)^3569
        have hw : |(-613090111/5000000000 : ℝ)|=(613090111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5859019331/10000000000 : ℝ)|^4593 ≤ (50258601210417/100000000000000 : ℝ)^3569
        have hw : |(5859019331/10000000000 : ℝ)|=(5859019331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_6 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596347843/5000000000 : ℝ)*x 0 + (1464755163/2500000000 : ℝ)*x 1 + (-1226179441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596347843/5000000000 : ℝ)^4593 ≤ (43026378024383/100000000000000 : ℝ)^3569 := by
    have hnat : (2596347843 : ℕ)^4593*100000000000000^3569 ≤ 43026378024383^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596347843 5000000000 43026378024383 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464755163/2500000000 : ℝ)^4593 ≤ (25129307896563/50000000000000 : ℝ)^3569 := by
    have hnat : (1464755163 : ℕ)^4593*50000000000000^3569 ≤ 25129307896563^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464755163 2500000000 25129307896563 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1226179441/10000000000 : ℝ)^4593 ≤ (3357503088559/50000000000000 : ℝ)^3569 := by
    have hnat : (1226179441 : ℕ)^4593*50000000000000^3569 ≤ 3357503088559^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226179441 10000000000 3357503088559 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596347843/5000000000 : ℝ), (1464755163/2500000000 : ℝ), (-1226179441/10000000000 : ℝ)] ![(43026378024383/100000000000000 : ℝ), (25129307896563/50000000000000 : ℝ), (3357503088559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596347843/5000000000 : ℝ)|^4593 ≤ (43026378024383/100000000000000 : ℝ)^3569
        have hw : |(2596347843/5000000000 : ℝ)|=(2596347843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1464755163/2500000000 : ℝ)|^4593 ≤ (25129307896563/50000000000000 : ℝ)^3569
        have hw : |(1464755163/2500000000 : ℝ)|=(1464755163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1226179441/10000000000 : ℝ)|^4593 ≤ (3357503088559/50000000000000 : ℝ)^3569
        have hw : |(-1226179441/10000000000 : ℝ)|=(1226179441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s0_7 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517883743/1250000000 : ℝ)*x 0 + (2696486329/5000000000 : ℝ)*x 1 + (197126633/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517883743/1250000000 : ℝ)^4593 ≤ (32175569590327/100000000000000 : ℝ)^3569 := by
    have hnat : (517883743 : ℕ)^4593*100000000000000^3569 ≤ 32175569590327^3569*1250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517883743 1250000000 32175569590327 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696486329/5000000000 : ℝ)^4593 ≤ (9034740435857/20000000000000 : ℝ)^3569 := by
    have hnat : (2696486329 : ℕ)^4593*20000000000000^3569 ≤ 9034740435857^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696486329 5000000000 9034740435857 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197126633/625000000 : ℝ)^4593 ≤ (22650728223753/100000000000000 : ℝ)^3569 := by
    have hnat : (197126633 : ℕ)^4593*100000000000000^3569 ≤ 22650728223753^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197126633 625000000 22650728223753 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517883743/1250000000 : ℝ), (2696486329/5000000000 : ℝ), (197126633/625000000 : ℝ)] ![(32175569590327/100000000000000 : ℝ), (9034740435857/20000000000000 : ℝ), (22650728223753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517883743/1250000000 : ℝ)|^4593 ≤ (32175569590327/100000000000000 : ℝ)^3569
        have hw : |(517883743/1250000000 : ℝ)|=(517883743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696486329/5000000000 : ℝ)|^4593 ≤ (9034740435857/20000000000000 : ℝ)^3569
        have hw : |(2696486329/5000000000 : ℝ)|=(2696486329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197126633/625000000 : ℝ)|^4593 ≤ (22650728223753/100000000000000 : ℝ)^3569
        have hw : |(197126633/625000000 : ℝ)|=(197126633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1548_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12513/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4591/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4591 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4591*1^1024 ≤ 0^1024*1^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4591/1024 : ℝ) ≤ (328780750564316891/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4591 ≤ (328780750564316891/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4591*20000000000000000000^1024 ≤ 328780750564316891^1024*5^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 328780750564316891 20000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (328780750564316891/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4591 := by
      have hnat : (1 : ℕ)^1024*1^4591 ≤ 1^4591*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20328780750564316891/20000000000000000000 : ℝ) ≤ (10036434560878399/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (20328780750564316891/20000000000000000000 : ℝ)^1024 ≤ (10036434560878399/10000000000000000 : ℝ)^4591 := by
      have hnat : (20328780750564316891 : ℕ)^1024*10000000000000000^4591 ≤ 10036434560878399^4591*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20328780750564316891 20000000000000000000 10036434560878399 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10036434560878399/10000000000000000 : ℝ)) (X := (20328780750564316891/20000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10328780750564316891/10000000000000000000 : ℝ) ≤ (5036434560878399/5000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (10328780750564316891/10000000000000000000 : ℝ)^1024 ≤ (5036434560878399/5000000000000000 : ℝ)^4591 := by
      have hnat : (10328780750564316891 : ℕ)^1024*5000000000000000^4591 ≤ 5036434560878399^4591*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10328780750564316891 10000000000000000000 5036434560878399 5000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036434560878399/5000000000000000 : ℝ)) (X := (10328780750564316891/10000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(36434560878399/4000000000000000 : ℝ)*(0 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36434560878399/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(328780750564316891/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(36434560878399/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4591/1024 : ℝ) := by
    rw [show (1 : ℝ)+(36434560878399/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10036434560878399/10000000000000000 : ℝ) by norm_num, show 1+(328780750564316891/20000000000000000000 : ℝ)+(0 : ℝ)=(20328780750564316891/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(328780750564316891/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(36434560878399/4000000000000000 : ℝ)*(2/5 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36434560878399/4000000000000000 : ℝ)*(2/5 : ℝ)=(5036434560878399/5000000000000000 : ℝ) by norm_num, show 1+2*(328780750564316891/20000000000000000000 : ℝ)=(10328780750564316891/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(36434560878399/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36434560878399/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(36434560878399/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36434560878399/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(36434560878399/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36434560878399/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-824154537/5000000000 : ℝ)*X 0 0+(5885643537/10000000000 : ℝ)*X 0 1+(2435208401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((341886927/625000000 : ℝ)*X 1 0+(-2214782683/10000000000 : ℝ)*X 1 1+(4870416799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((341886929/625000000 : ℝ)*X 2 0+(4870416761/10000000000 : ℝ)*X 2 1+(-69211959/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4135572823/10000000000 : ℝ)*X 0 0+(193257543/625000000 : ℝ)*X 0 1+(272637579/500000000 : ℝ)*X 0 2+(4135572823/10000000000 : ℝ)*X 1 0+(193257543/625000000 : ℝ)*X 1 1+(272637579/500000000 : ℝ)*X 1 2+(4135572823/10000000000 : ℝ)*X 2 0+(193257543/625000000 : ℝ)*X 2 1+(272637579/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41288357/250000000 : ℝ)*X 0 0+(306007817/625000000 : ℝ)*X 0 1+(5859019703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((649087067/1250000000 : ℝ)*X 1 0+(-613090111/5000000000 : ℝ)*X 1 1+(5859019331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2596347843/5000000000 : ℝ)*X 2 0+(1464755163/2500000000 : ℝ)*X 2 1+(-1226179441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((517883743/1250000000 : ℝ)*X 0 0+(2696486329/5000000000 : ℝ)*X 0 1+(197126633/625000000 : ℝ)*X 0 2+(517883743/1250000000 : ℝ)*X 1 0+(2696486329/5000000000 : ℝ)*X 1 1+(197126633/625000000 : ℝ)*X 1 2+(517883743/1250000000 : ℝ)*X 2 0+(2696486329/5000000000 : ℝ)*X 2 1+(197126633/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8227046438291477607/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39737373/50000000000000 : ℝ)*(base1) + (1756940293/100000000000000 : ℝ)*(base19) + (1762702503/100000000000000 : ℝ)*(base23) + (2845097/1250000000000 : ℝ)*(upper3) + (227601803/100000000000000 : ℝ)*(upper5) + (176079420273107/25000000000000 : ℝ)*(major0) + (176079420273107/25000000000000 : ℝ)*(major1) + (176079420273107/25000000000000 : ℝ)*(major2) + (985007721864341/100000000000000 : ℝ)*(sp0) + (985012304875769/100000000000000 : ℝ)*(sp1) + (492506149556779/50000000000000 : ℝ)*(sp2) + (211809092650739/50000000000000 : ℝ)*(sp3) + (3209713233/50000000000000 : ℝ)*(sp4) + (552271537/20000000000000 : ℝ)*(sp7) + (423621026133909/100000000000000 : ℝ)*(f.failure) + (985014061816061/100000000000000 : ℝ)*(f.sum) + (128573030915693/50000000000000000000000000000 : ℝ)*base65 + (484365929384307/100000000000000000000000000000 : ℝ)*base68 + (40848203084307/100000000000000000000000000000 : ℝ)*base70 + (311753787284307/100000000000000000000000000000 : ℝ)*base72 + (112244128565693/50000000000000000000000000000 : ℝ)*base73 + (992940838184307/100000000000000000000000000000 : ℝ)*base76 + (290492217684307/100000000000000000000000000000 : ℝ)*base78 + (292883526284307/100000000000000000000000000000 : ℝ)*base80 + (311069146115693/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2065603/5000000000000000000000 : ℝ)*base90 + (2065603/5000000000000000000000 : ℝ)*base92 + (2065603/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (433768289547997412584113/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51312813/10000000000000 : ℝ)*(base19) + (401707523/50000000000000 : ℝ)*(base23) + (493194539/100000000000000 : ℝ)*(base39) + (14505671/100000000000000 : ℝ)*(upper3) + (84732421/25000000000000 : ℝ)*(upper5) + (46411583810141/6250000000000 : ℝ)*(major0) + (46411583810141/6250000000000 : ℝ)*(major1) + (742584847767717/100000000000000 : ℝ)*(major2) + (322366737/20000000000000 : ℝ)*(sp1) + (115790349/10000000000000 : ℝ)*(sp2) + (41541300350177/4000000000000 : ℝ)*(sp4) + (103853038379261/10000000000000 : ℝ)*(sp5) + (519265520315213/50000000000000 : ℝ)*(sp6) + (446637607680827/100000000000000 : ℝ)*(sp7) + (446637607680827/100000000000000 : ℝ)*(f.failure) + (1038533001948963/100000000000000 : ℝ)*(f.sum) + (426152775646773/400000000000000000000000000000 : ℝ)*base66 + (1075314871554917/400000000000000000000000000000 : ℝ)*base68 + (47971886730741/25000000000000000000000000000 : ℝ)*base70 + (1229218407645083/400000000000000000000000000000 : ℝ)*base71 + (2328719656846773/400000000000000000000000000000 : ℝ)*base74 + (88961447980741/25000000000000000000000000000 : ℝ)*base76 + (147404671944259/25000000000000000000000000000 : ℝ)*base77 + (270885658844259/25000000000000000000000000000 : ℝ)*base79 + (47514731830741/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (10473491/5000000000000000000000 : ℝ)*base89 + (10473491/5000000000000000000000 : ℝ)*base91 + (10473491/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1548_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12513/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1548_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1548_s1_0 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-448134607/2500000000 : ℝ)*x 0 + (5547704757/10000000000 : ℝ)*x 1 + (1023099637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448134607/2500000000 : ℝ)^4593 ≤ (547327551309/5000000000000 : ℝ)^3569 := by
    have hnat : (448134607 : ℕ)^4593*5000000000000^3569 ≤ 547327551309^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448134607 2500000000 547327551309 5000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5547704757/10000000000 : ℝ)^4593 ≤ (46848489539457/100000000000000 : ℝ)^3569 := by
    have hnat : (5547704757 : ℕ)^4593*100000000000000^3569 ≤ 46848489539457^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547704757 10000000000 46848489539457 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023099637/2000000000 : ℝ)^4593 ≤ (42204959415483/100000000000000 : ℝ)^3569 := by
    have hnat : (1023099637 : ℕ)^4593*100000000000000^3569 ≤ 42204959415483^3569*2000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023099637 2000000000 42204959415483 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448134607/2500000000 : ℝ), (5547704757/10000000000 : ℝ), (1023099637/2000000000 : ℝ)] ![(547327551309/5000000000000 : ℝ), (46848489539457/100000000000000 : ℝ), (42204959415483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448134607/2500000000 : ℝ)|^4593 ≤ (547327551309/5000000000000 : ℝ)^3569
        have hw : |(-448134607/2500000000 : ℝ)|=(448134607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5547704757/10000000000 : ℝ)|^4593 ≤ (46848489539457/100000000000000 : ℝ)^3569
        have hw : |(5547704757/10000000000 : ℝ)|=(5547704757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023099637/2000000000 : ℝ)|^4593 ≤ (42204959415483/100000000000000 : ℝ)^3569
        have hw : |(1023099637/2000000000 : ℝ)|=(1023099637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_1 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076042069/2000000000 : ℝ)*x 0 + (-1009577639/5000000000 : ℝ)*x 1 + (5115497221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076042069/2000000000 : ℝ)^4593 ≤ (45036174786733/100000000000000 : ℝ)^3569 := by
    have hnat : (1076042069 : ℕ)^4593*100000000000000^3569 ≤ 45036174786733^3569*2000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076042069 2000000000 45036174786733 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009577639/5000000000 : ℝ)^4593 ≤ (797429751119/6250000000000 : ℝ)^3569 := by
    have hnat : (1009577639 : ℕ)^4593*6250000000000^3569 ≤ 797429751119^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009577639 5000000000 797429751119 6250000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5115497221/10000000000 : ℝ)^4593 ≤ (21102474590069/50000000000000 : ℝ)^3569 := by
    have hnat : (5115497221 : ℕ)^4593*50000000000000^3569 ≤ 21102474590069^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115497221 10000000000 21102474590069 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076042069/2000000000 : ℝ), (-1009577639/5000000000 : ℝ), (5115497221/10000000000 : ℝ)] ![(45036174786733/100000000000000 : ℝ), (797429751119/6250000000000 : ℝ), (21102474590069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076042069/2000000000 : ℝ)|^4593 ≤ (45036174786733/100000000000000 : ℝ)^3569
        have hw : |(1076042069/2000000000 : ℝ)|=(1076042069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009577639/5000000000 : ℝ)|^4593 ≤ (797429751119/6250000000000 : ℝ)^3569
        have hw : |(-1009577639/5000000000 : ℝ)|=(1009577639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5115497221/10000000000 : ℝ)|^4593 ≤ (21102474590069/50000000000000 : ℝ)^3569
        have hw : |(5115497221/10000000000 : ℝ)|=(5115497221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_2 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345052441/2500000000 : ℝ)*x 0 + (5115497617/10000000000 : ℝ)*x 1 + (-2019155531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345052441/2500000000 : ℝ)^4593 ≤ (45036168527973/100000000000000 : ℝ)^3569 := by
    have hnat : (1345052441 : ℕ)^4593*100000000000000^3569 ≤ 45036168527973^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345052441 2500000000 45036168527973 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5115497617/10000000000 : ℝ)^4593 ≤ (42204953384699/100000000000000 : ℝ)^3569 := by
    have hnat : (5115497617 : ℕ)^4593*100000000000000^3569 ≤ 42204953384699^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115497617 10000000000 42204953384699 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019155531/10000000000 : ℝ)^4593 ≤ (12758878075277/100000000000000 : ℝ)^3569 := by
    have hnat : (2019155531 : ℕ)^4593*100000000000000^3569 ≤ 12758878075277^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019155531 10000000000 12758878075277 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345052441/2500000000 : ℝ), (5115497617/10000000000 : ℝ), (-2019155531/10000000000 : ℝ)] ![(45036168527973/100000000000000 : ℝ), (42204953384699/100000000000000 : ℝ), (12758878075277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345052441/2500000000 : ℝ)|^4593 ≤ (45036168527973/100000000000000 : ℝ)^3569
        have hw : |(1345052441/2500000000 : ℝ)|=(1345052441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5115497617/10000000000 : ℝ)|^4593 ≤ (42204953384699/100000000000000 : ℝ)^3569
        have hw : |(5115497617/10000000000 : ℝ)|=(5115497617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2019155531/10000000000 : ℝ)|^4593 ≤ (12758878075277/100000000000000 : ℝ)^3569
        have hw : |(-2019155531/10000000000 : ℝ)|=(2019155531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_3 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118237837/5000000000 : ℝ)*x 0 + (3758431301/10000000000 : ℝ)*x 1 + (4763409117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118237837/5000000000 : ℝ)^4593 ≤ (264896807483/800000000000 : ℝ)^3569 := by
    have hnat : (2118237837 : ℕ)^4593*800000000000^3569 ≤ 264896807483^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118237837 5000000000 264896807483 800000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3758431301/10000000000 : ℝ)^4593 ≤ (227069907583/800000000000 : ℝ)^3569 := by
    have hnat : (3758431301 : ℕ)^4593*800000000000^3569 ≤ 227069907583^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758431301 10000000000 227069907583 800000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4763409117/10000000000 : ℝ)^4593 ≤ (38504160606049/100000000000000 : ℝ)^3569 := by
    have hnat : (4763409117 : ℕ)^4593*100000000000000^3569 ≤ 38504160606049^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4763409117 10000000000 38504160606049 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118237837/5000000000 : ℝ), (3758431301/10000000000 : ℝ), (4763409117/10000000000 : ℝ)] ![(264896807483/800000000000 : ℝ), (227069907583/800000000000 : ℝ), (38504160606049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118237837/5000000000 : ℝ)|^4593 ≤ (264896807483/800000000000 : ℝ)^3569
        have hw : |(2118237837/5000000000 : ℝ)|=(2118237837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3758431301/10000000000 : ℝ)|^4593 ≤ (227069907583/800000000000 : ℝ)^3569
        have hw : |(3758431301/10000000000 : ℝ)|=(3758431301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4763409117/10000000000 : ℝ)|^4593 ≤ (38504160606049/100000000000000 : ℝ)^3569
        have hw : |(4763409117/10000000000 : ℝ)|=(4763409117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_4 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-358556173/2000000000 : ℝ)*x 0 + (2560046521/5000000000 : ℝ)*x 1 + (5543039133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358556173/2000000000 : ℝ)^4593 ≤ (5474228168987/50000000000000 : ℝ)^3569 := by
    have hnat : (358556173 : ℕ)^4593*50000000000000^3569 ≤ 5474228168987^3569*2000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358556173 2000000000 5474228168987 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560046521/5000000000 : ℝ)^4593 ≤ (42253751951989/100000000000000 : ℝ)^3569 := by
    have hnat : (2560046521 : ℕ)^4593*100000000000000^3569 ≤ 42253751951989^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560046521 5000000000 42253751951989 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5543039133/10000000000 : ℝ)^4593 ≤ (46797791697141/100000000000000 : ℝ)^3569 := by
    have hnat : (5543039133 : ℕ)^4593*100000000000000^3569 ≤ 46797791697141^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543039133 10000000000 46797791697141 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-358556173/2000000000 : ℝ), (2560046521/5000000000 : ℝ), (5543039133/10000000000 : ℝ)] ![(5474228168987/50000000000000 : ℝ), (42253751951989/100000000000000 : ℝ), (46797791697141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-358556173/2000000000 : ℝ)|^4593 ≤ (5474228168987/50000000000000 : ℝ)^3569
        have hw : |(-358556173/2000000000 : ℝ)|=(358556173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2560046521/5000000000 : ℝ)|^4593 ≤ (42253751951989/100000000000000 : ℝ)^3569
        have hw : |(2560046521/5000000000 : ℝ)|=(2560046521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5543039133/10000000000 : ℝ)|^4593 ≤ (46797791697141/100000000000000 : ℝ)^3569
        have hw : |(5543039133/10000000000 : ℝ)|=(5543039133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_5 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632951429/5000000000 : ℝ)*x 0 + (-795807619/5000000000 : ℝ)*x 1 + (1385759733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632951429/5000000000 : ℝ)^4593 ≤ (21904290973379/50000000000000 : ℝ)^3569 := by
    have hnat : (2632951429 : ℕ)^4593*50000000000000^3569 ≤ 21904290973379^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632951429 5000000000 21904290973379 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795807619/5000000000 : ℝ)^4593 ≤ (9393628526551/100000000000000 : ℝ)^3569 := by
    have hnat : (795807619 : ℕ)^4593*100000000000000^3569 ≤ 9393628526551^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795807619 5000000000 9393628526551 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385759733/2500000000 : ℝ)^4593 ≤ (5849723689161/12500000000000 : ℝ)^3569 := by
    have hnat : (1385759733 : ℕ)^4593*12500000000000^3569 ≤ 5849723689161^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385759733 2500000000 5849723689161 12500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632951429/5000000000 : ℝ), (-795807619/5000000000 : ℝ), (1385759733/2500000000 : ℝ)] ![(21904290973379/50000000000000 : ℝ), (9393628526551/100000000000000 : ℝ), (5849723689161/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632951429/5000000000 : ℝ)|^4593 ≤ (21904290973379/50000000000000 : ℝ)^3569
        have hw : |(2632951429/5000000000 : ℝ)|=(2632951429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-795807619/5000000000 : ℝ)|^4593 ≤ (9393628526551/100000000000000 : ℝ)^3569
        have hw : |(-795807619/5000000000 : ℝ)|=(795807619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1385759733/2500000000 : ℝ)|^4593 ≤ (5849723689161/12500000000000 : ℝ)^3569
        have hw : |(1385759733/2500000000 : ℝ)|=(1385759733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_6 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265904181/10000000000 : ℝ)*x 0 + (2771519349/5000000000 : ℝ)*x 1 + (-1591613707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265904181/10000000000 : ℝ)^4593 ≤ (43808596111091/100000000000000 : ℝ)^3569 := by
    have hnat : (5265904181 : ℕ)^4593*100000000000000^3569 ≤ 43808596111091^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265904181 10000000000 43808596111091 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771519349/5000000000 : ℝ)^4593 ≤ (46797786970893/100000000000000 : ℝ)^3569 := by
    have hnat : (2771519349 : ℕ)^4593*100000000000000^3569 ≤ 46797786970893^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771519349 5000000000 46797786970893 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1591613707/10000000000 : ℝ)^4593 ≤ (9393616898141/100000000000000 : ℝ)^3569 := by
    have hnat : (1591613707 : ℕ)^4593*100000000000000^3569 ≤ 9393616898141^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591613707 10000000000 9393616898141 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265904181/10000000000 : ℝ), (2771519349/5000000000 : ℝ), (-1591613707/10000000000 : ℝ)] ![(43808596111091/100000000000000 : ℝ), (46797786970893/100000000000000 : ℝ), (9393616898141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265904181/10000000000 : ℝ)|^4593 ≤ (43808596111091/100000000000000 : ℝ)^3569
        have hw : |(5265904181/10000000000 : ℝ)|=(5265904181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771519349/5000000000 : ℝ)|^4593 ≤ (46797786970893/100000000000000 : ℝ)^3569
        have hw : |(2771519349/5000000000 : ℝ)|=(2771519349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1591613707/10000000000 : ℝ)|^4593 ≤ (9393616898141/100000000000000 : ℝ)^3569
        have hw : |(-1591613707/10000000000 : ℝ)|=(1591613707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s1_7 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118518851/5000000000 : ℝ)*x 0 + (2376361397/5000000000 : ℝ)*x 1 + (1884639789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118518851/5000000000 : ℝ)^4593 ≤ (33117754184643/100000000000000 : ℝ)^3569 := by
    have hnat : (2118518851 : ℕ)^4593*100000000000000^3569 ≤ 33117754184643^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118518851 5000000000 33117754184643 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2376361397/5000000000 : ℝ)^4593 ≤ (19196515713963/50000000000000 : ℝ)^3569 := by
    have hnat : (2376361397 : ℕ)^4593*50000000000000^3569 ≤ 19196515713963^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376361397 5000000000 19196515713963 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884639789/5000000000 : ℝ)^4593 ≤ (7122303591399/25000000000000 : ℝ)^3569 := by
    have hnat : (1884639789 : ℕ)^4593*25000000000000^3569 ≤ 7122303591399^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884639789 5000000000 7122303591399 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118518851/5000000000 : ℝ), (2376361397/5000000000 : ℝ), (1884639789/5000000000 : ℝ)] ![(33117754184643/100000000000000 : ℝ), (19196515713963/50000000000000 : ℝ), (7122303591399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118518851/5000000000 : ℝ)|^4593 ≤ (33117754184643/100000000000000 : ℝ)^3569
        have hw : |(2118518851/5000000000 : ℝ)|=(2118518851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2376361397/5000000000 : ℝ)|^4593 ≤ (19196515713963/50000000000000 : ℝ)^3569
        have hw : |(2376361397/5000000000 : ℝ)|=(2376361397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1884639789/5000000000 : ℝ)|^4593 ≤ (7122303591399/25000000000000 : ℝ)^3569
        have hw : |(1884639789/5000000000 : ℝ)|=(1884639789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1548_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12513/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4407/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8981/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12513/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12513/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12513/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12513/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12513/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12513/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3279/100000 : ℝ) ^ (4591/1024 : ℝ) ≤ (22155287325809/100000000000000000000 : ℝ) := by
    have hpowers : (3279/100000 : ℝ)^4591 ≤ (22155287325809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3279 : ℕ)^4591*100000000000000000000^1024 ≤ 22155287325809^1024*100000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3279 100000 22155287325809 100000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3279/100000 : ℝ)) (X := (22155287325809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12513/50000 : ℝ) ^ (4591/1024 : ℝ) ≤ (100396628225585531/50000000000000000000 : ℝ) := by
    have hpowers : (12513/50000 : ℝ)^4591 ≤ (100396628225585531/50000000000000000000 : ℝ)^1024 := by
      have hnat : (12513 : ℕ)^4591*50000000000000000000^1024 ≤ 100396628225585531^1024*50000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12513 50000 100396628225585531 50000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12513/50000 : ℝ)) (X := (100396628225585531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000022155287325809/50000000000000000000 : ℝ) ≤ (5000000494162717/5000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (50000022155287325809/50000000000000000000 : ℝ)^1024 ≤ (5000000494162717/5000000000000000 : ℝ)^4591 := by
      have hnat : (50000022155287325809 : ℕ)^1024*5000000000000000^4591 ≤ 5000000494162717^4591*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000022155287325809 50000000000000000000 5000000494162717 5000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000494162717/5000000000000000 : ℝ)) (X := (50000022155287325809/50000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100200815411738496871/100000000000000000000 : ℝ) ≤ (10004475599034467/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (100200815411738496871/100000000000000000000 : ℝ)^1024 ≤ (10004475599034467/10000000000000000 : ℝ)^4591 := by
      have hnat : (100200815411738496871 : ℕ)^1024*10000000000000000^4591 ≤ 10004475599034467^4591*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100200815411738496871 100000000000000000000 10004475599034467 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004475599034467/10000000000000000 : ℝ)) (X := (100200815411738496871/100000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25100396628225585531/25000000000000000000 : ℝ) ≤ (20017900419487/20000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (25100396628225585531/25000000000000000000 : ℝ)^1024 ≤ (20017900419487/20000000000000 : ℝ)^4591 := by
      have hnat : (25100396628225585531 : ℕ)^1024*20000000000000^4591 ≤ 20017900419487^4591*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25100396628225585531 25000000000000000000 20017900419487 20000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20017900419487/20000000000000 : ℝ)) (X := (25100396628225585531/25000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(22155287325809/100000000000000000000 : ℝ) ≤ ((1132503526021267577/1132656250000000000 : ℝ)+2*(1491536903011/724900000000000 : ℝ)*(3279/100000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (1132503526021267577/1132656250000000000 : ℝ)+2*(1491536903011/724900000000000 : ℝ)*(3279/100000 : ℝ)=(5000000494162717/5000000000000000 : ℝ) by norm_num, show 1+2*(22155287325809/100000000000000000000 : ℝ)=(50000022155287325809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100396628225585531/50000000000000000000 : ℝ)+(22155287325809/100000000000000000000 : ℝ) ≤ ((1132503526021267577/1132656250000000000 : ℝ)+(1491536903011/724900000000000 : ℝ)*((12513/50000 : ℝ)+(3279/100000 : ℝ)))^(4591/1024 : ℝ) := by
    rw [show (1132503526021267577/1132656250000000000 : ℝ)+(1491536903011/724900000000000 : ℝ)*((12513/50000 : ℝ)+(3279/100000 : ℝ))=(10004475599034467/10000000000000000 : ℝ) by norm_num, show 1+(100396628225585531/50000000000000000000 : ℝ)+(22155287325809/100000000000000000000 : ℝ)=(100200815411738496871/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100396628225585531/50000000000000000000 : ℝ) ≤ ((1132503526021267577/1132656250000000000 : ℝ)+2*(1491536903011/724900000000000 : ℝ)*(12513/50000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (1132503526021267577/1132656250000000000 : ℝ)+2*(1491536903011/724900000000000 : ℝ)*(12513/50000 : ℝ)=(20017900419487/20000000000000 : ℝ) by norm_num, show 1+2*(100396628225585531/50000000000000000000 : ℝ)=(25100396628225585531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1132503526021267577/1132656250000000000 : ℝ)*(X 1 0+X 2 0)+(1491536903011/724900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (3279/100000 : ℝ)) (hi := (12513/50000 : ℝ)) (c := (1132503526021267577/1132656250000000000 : ℝ)) (alpha := (1491536903011/724900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1132503526021267577/1132656250000000000 : ℝ)*(X 0 1+X 2 1)+(1491536903011/724900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (3279/100000 : ℝ)) (hi := (12513/50000 : ℝ)) (c := (1132503526021267577/1132656250000000000 : ℝ)) (alpha := (1491536903011/724900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1132503526021267577/1132656250000000000 : ℝ)*(X 0 2+X 1 2)+(1491536903011/724900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (3279/100000 : ℝ)) (hi := (12513/50000 : ℝ)) (c := (1132503526021267577/1132656250000000000 : ℝ)) (alpha := (1491536903011/724900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-448134607/2500000000 : ℝ)*X 0 0+(5547704757/10000000000 : ℝ)*X 0 1+(1023099637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1076042069/2000000000 : ℝ)*X 1 0+(-1009577639/5000000000 : ℝ)*X 1 1+(5115497221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1345052441/2500000000 : ℝ)*X 2 0+(5115497617/10000000000 : ℝ)*X 2 1+(-2019155531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118237837/5000000000 : ℝ)*X 0 0+(3758431301/10000000000 : ℝ)*X 0 1+(4763409117/10000000000 : ℝ)*X 0 2+(2118237837/5000000000 : ℝ)*X 1 0+(3758431301/10000000000 : ℝ)*X 1 1+(4763409117/10000000000 : ℝ)*X 1 2+(2118237837/5000000000 : ℝ)*X 2 0+(3758431301/10000000000 : ℝ)*X 2 1+(4763409117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-358556173/2000000000 : ℝ)*X 0 0+(2560046521/5000000000 : ℝ)*X 0 1+(5543039133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632951429/5000000000 : ℝ)*X 1 0+(-795807619/5000000000 : ℝ)*X 1 1+(1385759733/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265904181/10000000000 : ℝ)*X 2 0+(2771519349/5000000000 : ℝ)*X 2 1+(-1591613707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118518851/5000000000 : ℝ)*X 0 0+(2376361397/5000000000 : ℝ)*X 0 1+(1884639789/5000000000 : ℝ)*X 0 2+(2118518851/5000000000 : ℝ)*X 1 0+(2376361397/5000000000 : ℝ)*X 1 1+(1884639789/5000000000 : ℝ)*X 1 2+(2118518851/5000000000 : ℝ)*X 2 0+(2376361397/5000000000 : ℝ)*X 2 1+(1884639789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10853495248844130992356359/2574218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2331129/3125000000000 : ℝ)*(base1) + (534754817/100000000000000 : ℝ)*(base19) + (87604371/100000000000000 : ℝ)*(base23) + (2763983/4000000000000 : ℝ)*(lower2) + (5089423/100000000000000 : ℝ)*(upper5) + (827188940242423/50000000000000 : ℝ)*(major0) + (827188940242423/50000000000000 : ℝ)*(major1) + (827188940242423/50000000000000 : ℝ)*(major2) + (231370861022469/10000000000000 : ℝ)*(sp0) + (144606750054609/6250000000000 : ℝ)*(sp1) + (578426301671417/25000000000000 : ℝ)*(sp2) + (995047001246519/100000000000000 : ℝ)*(sp3) + (1620669261/50000000000000 : ℝ)*(sp6) + (8957517/100000000000000 : ℝ)*(sp7) + (248761771200041/25000000000000 : ℝ)*(f.failure) + (1156854267814281/50000000000000 : ℝ)*(f.sum) + (8780934828027/1647500000000000000000000000 : ℝ)*base66 + (1514675394446417/643554687500000000000000000000 : ℝ)*base67 + (2441776961665167/643554687500000000000000000000 : ℝ)*base69 + (37323345626658297/10296875000000000000000000000000 : ℝ)*base71 + (8713527613229/3295000000000000000000000000 : ℝ)*base74 + (25369054341243211/5148437500000000000000000000000 : ℝ)*base75 + (40736657818435453/10296875000000000000000000000000 : ℝ)*base78 + (30989890554493211/5148437500000000000000000000000 : ℝ)*base79 + (8919919500319/3295000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2955953/1250000000000000000000 : ℝ)*base89 + (2955953/1250000000000000000000 : ℝ)*base91 + (2955953/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22105454518114325620351713/14158203125000000000000000000000 : ℝ) := by norm_num
    linear_combination (45280681/100000000000000 : ℝ)*(base19) + (310425883/50000000000000 : ℝ)*(base23) + (72010721/100000000000000 : ℝ)*(upper4) + (275853469/100000000000000 : ℝ)*(upper5) + (422651696050641/25000000000000 : ℝ)*(major0) + (422651696050641/25000000000000 : ℝ)*(major1) + (422651696050641/25000000000000 : ℝ)*(major2) + (63953023/10000000000000 : ℝ)*(sp0) + (2724888317/50000000000000 : ℝ)*(sp2) + (609744667/50000000000000 : ℝ)*(sp3) + (147773465429841/6250000000000 : ℝ)*(sp4) + (1182188020563503/50000000000000 : ℝ)*(sp5) + (1182185007889643/50000000000000 : ℝ)*(sp6) + (508418105232087/50000000000000 : ℝ)*(sp7) + (1016837429953507/100000000000000 : ℝ)*(f.failure) + (1182188043203843/50000000000000 : ℝ)*(f.sum) + (13285220048219/9061250000000000000000000000 : ℝ)*base66 + (166029557316919411/56632812500000000000000000000000 : ℝ)*base68 + (464247974677106911/56632812500000000000000000000000 : ℝ)*base70 + (689777818594575661/56632812500000000000000000000000 : ℝ)*base72 + (15181681782007/18122500000000000000000000000 : ℝ)*base73 + (95787239146265317/7079101562500000000000000000000 : ℝ)*base76 + (332148395197701893/28316406250000000000000000000000 : ℝ)*base78 + (450639203164231911/56632812500000000000000000000000 : ℝ)*base80 + (51694919729163/18122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2520069/5000000000000000000000 : ℝ)*base90 + (2520069/5000000000000000000000 : ℝ)*base92 + (2520069/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1548_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12513/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8981/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1548_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1548_s2_0 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813212359/10000000000 : ℝ)*x 0 + (2723616817/5000000000 : ℝ)*x 1 + (5202527419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813212359/10000000000 : ℝ)^4593 ≤ (11109292332993/100000000000000 : ℝ)^3569 := by
    have hnat : (1813212359 : ℕ)^4593*100000000000000^3569 ≤ 11109292332993^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813212359 10000000000 11109292332993 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723616817/5000000000 : ℝ)^4593 ≤ (45759462402483/100000000000000 : ℝ)^3569 := by
    have hnat : (2723616817 : ℕ)^4593*100000000000000^3569 ≤ 45759462402483^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723616817 5000000000 45759462402483 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5202527419/10000000000 : ℝ)^4593 ≤ (10782811312827/25000000000000 : ℝ)^3569 := by
    have hnat : (5202527419 : ℕ)^4593*25000000000000^3569 ≤ 10782811312827^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202527419 10000000000 10782811312827 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813212359/10000000000 : ℝ), (2723616817/5000000000 : ℝ), (5202527419/10000000000 : ℝ)] ![(11109292332993/100000000000000 : ℝ), (45759462402483/100000000000000 : ℝ), (10782811312827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813212359/10000000000 : ℝ)|^4593 ≤ (11109292332993/100000000000000 : ℝ)^3569
        have hw : |(-1813212359/10000000000 : ℝ)|=(1813212359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723616817/5000000000 : ℝ)|^4593 ≤ (45759462402483/100000000000000 : ℝ)^3569
        have hw : |(2723616817/5000000000 : ℝ)|=(2723616817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5202527419/10000000000 : ℝ)|^4593 ≤ (10782811312827/25000000000000 : ℝ)^3569
        have hw : |(5202527419/10000000000 : ℝ)|=(5202527419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_1 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354411381/10000000000 : ℝ)*x 0 + (-969468573/5000000000 : ℝ)*x 1 + (650315953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354411381/10000000000 : ℝ)^4593 ≤ (22379224818833/50000000000000 : ℝ)^3569 := by
    have hnat : (5354411381 : ℕ)^4593*50000000000000^3569 ≤ 22379224818833^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354411381 10000000000 22379224818833 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969468573/5000000000 : ℝ)^4593 ≤ (6055151451987/50000000000000 : ℝ)^3569 := by
    have hnat : (969468573 : ℕ)^4593*50000000000000^3569 ≤ 6055151451987^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969468573 5000000000 6055151451987 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650315953/1250000000 : ℝ)^4593 ≤ (5391405929809/12500000000000 : ℝ)^3569 := by
    have hnat : (650315953 : ℕ)^4593*12500000000000^3569 ≤ 5391405929809^3569*1250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650315953 1250000000 5391405929809 12500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354411381/10000000000 : ℝ), (-969468573/5000000000 : ℝ), (650315953/1250000000 : ℝ)] ![(22379224818833/50000000000000 : ℝ), (6055151451987/50000000000000 : ℝ), (5391405929809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354411381/10000000000 : ℝ)|^4593 ≤ (22379224818833/50000000000000 : ℝ)^3569
        have hw : |(5354411381/10000000000 : ℝ)|=(5354411381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969468573/5000000000 : ℝ)|^4593 ≤ (6055151451987/50000000000000 : ℝ)^3569
        have hw : |(-969468573/5000000000 : ℝ)|=(969468573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650315953/1250000000 : ℝ)|^4593 ≤ (5391405929809/12500000000000 : ℝ)^3569
        have hw : |(650315953/1250000000 : ℝ)|=(650315953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_2 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677206037/5000000000 : ℝ)*x 0 + (1300631767/2500000000 : ℝ)*x 1 + (-1938936957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677206037/5000000000 : ℝ)^4593 ≤ (8951691418529/20000000000000 : ℝ)^3569 := by
    have hnat : (2677206037 : ℕ)^4593*20000000000000^3569 ≤ 8951691418529^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677206037 5000000000 8951691418529 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300631767/2500000000 : ℝ)^4593 ≤ (5391405188307/12500000000000 : ℝ)^3569 := by
    have hnat : (1300631767 : ℕ)^4593*12500000000000^3569 ≤ 5391405188307^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300631767 2500000000 5391405188307 12500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1938936957/10000000000 : ℝ)^4593 ≤ (756893836551/6250000000000 : ℝ)^3569 := by
    have hnat : (1938936957 : ℕ)^4593*6250000000000^3569 ≤ 756893836551^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938936957 10000000000 756893836551 6250000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677206037/5000000000 : ℝ), (1300631767/2500000000 : ℝ), (-1938936957/10000000000 : ℝ)] ![(8951691418529/20000000000000 : ℝ), (5391405188307/12500000000000 : ℝ), (756893836551/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677206037/5000000000 : ℝ)|^4593 ≤ (8951691418529/20000000000000 : ℝ)^3569
        have hw : |(2677206037/5000000000 : ℝ)|=(2677206037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300631767/2500000000 : ℝ)|^4593 ≤ (5391405188307/12500000000000 : ℝ)^3569
        have hw : |(1300631767/2500000000 : ℝ)|=(1300631767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1938936957/10000000000 : ℝ)|^4593 ≤ (756893836551/6250000000000 : ℝ)^3569
        have hw : |(-1938936957/10000000000 : ℝ)|=(1938936957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_3 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125703861/5000000000 : ℝ)*x 0 + (3974749259/10000000000 : ℝ)*x 1 + (4543748109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125703861/5000000000 : ℝ)^4593 ≤ (3326237036947/10000000000000 : ℝ)^3569 := by
    have hnat : (2125703861 : ℕ)^4593*10000000000000^3569 ≤ 3326237036947^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125703861 5000000000 3326237036947 10000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3974749259/10000000000 : ℝ)^4593 ≤ (15251608674149/50000000000000 : ℝ)^3569 := by
    have hnat : (3974749259 : ℕ)^4593*50000000000000^3569 ≤ 15251608674149^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3974749259 10000000000 15251608674149 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543748109/10000000000 : ℝ)^4593 ≤ (9058603064851/25000000000000 : ℝ)^3569 := by
    have hnat : (4543748109 : ℕ)^4593*25000000000000^3569 ≤ 9058603064851^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543748109 10000000000 9058603064851 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125703861/5000000000 : ℝ), (3974749259/10000000000 : ℝ), (4543748109/10000000000 : ℝ)] ![(3326237036947/10000000000000 : ℝ), (15251608674149/50000000000000 : ℝ), (9058603064851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125703861/5000000000 : ℝ)|^4593 ≤ (3326237036947/10000000000000 : ℝ)^3569
        have hw : |(2125703861/5000000000 : ℝ)|=(2125703861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3974749259/10000000000 : ℝ)|^4593 ≤ (15251608674149/50000000000000 : ℝ)^3569
        have hw : |(3974749259/10000000000 : ℝ)|=(3974749259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543748109/10000000000 : ℝ)|^4593 ≤ (9058603064851/25000000000000 : ℝ)^3569
        have hw : |(4543748109/10000000000 : ℝ)|=(4543748109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_4 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-226656993/1250000000 : ℝ)*x 0 + (5204008421/10000000000 : ℝ)*x 1 + (170179379/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226656993/1250000000 : ℝ)^4593 ≤ (2777408997691/25000000000000 : ℝ)^3569 := by
    have hnat : (226656993 : ℕ)^4593*25000000000000^3569 ≤ 2777408997691^3569*1250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226656993 1250000000 2777408997691 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204008421/10000000000 : ℝ)^4593 ≤ (43147046845191/100000000000000 : ℝ)^3569 := by
    have hnat : (5204008421 : ℕ)^4593*100000000000000^3569 ≤ 43147046845191^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204008421 10000000000 43147046845191 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170179379/312500000 : ℝ)^4593 ≤ (45743317155371/100000000000000 : ℝ)^3569 := by
    have hnat : (170179379 : ℕ)^4593*100000000000000^3569 ≤ 45743317155371^3569*312500000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170179379 312500000 45743317155371 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226656993/1250000000 : ℝ), (5204008421/10000000000 : ℝ), (170179379/312500000 : ℝ)] ![(2777408997691/25000000000000 : ℝ), (43147046845191/100000000000000 : ℝ), (45743317155371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226656993/1250000000 : ℝ)|^4593 ≤ (2777408997691/25000000000000 : ℝ)^3569
        have hw : |(-226656993/1250000000 : ℝ)|=(226656993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204008421/10000000000 : ℝ)|^4593 ≤ (43147046845191/100000000000000 : ℝ)^3569
        have hw : |(5204008421/10000000000 : ℝ)|=(5204008421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170179379/312500000 : ℝ)|^4593 ≤ (45743317155371/100000000000000 : ℝ)^3569
        have hw : |(170179379/312500000 : ℝ)|=(170179379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_5 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644919057/5000000000 : ℝ)*x 0 + (-1695724521/10000000000 : ℝ)*x 1 + (5445740101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644919057/5000000000 : ℝ)^4593 ≤ (8813001005777/20000000000000 : ℝ)^3569 := by
    have hnat : (2644919057 : ℕ)^4593*20000000000000^3569 ≤ 8813001005777^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644919057 5000000000 8813001005777 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1695724521/10000000000 : ℝ)^4593 ≤ (5095839041869/50000000000000 : ℝ)^3569 := by
    have hnat : (1695724521 : ℕ)^4593*50000000000000^3569 ≤ 5095839041869^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695724521 10000000000 5095839041869 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445740101/10000000000 : ℝ)^4593 ≤ (2858957303969/6250000000000 : ℝ)^3569 := by
    have hnat : (5445740101 : ℕ)^4593*6250000000000^3569 ≤ 2858957303969^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445740101 10000000000 2858957303969 6250000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644919057/5000000000 : ℝ), (-1695724521/10000000000 : ℝ), (5445740101/10000000000 : ℝ)] ![(8813001005777/20000000000000 : ℝ), (5095839041869/50000000000000 : ℝ), (2858957303969/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644919057/5000000000 : ℝ)|^4593 ≤ (8813001005777/20000000000000 : ℝ)^3569
        have hw : |(2644919057/5000000000 : ℝ)|=(2644919057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1695724521/10000000000 : ℝ)|^4593 ≤ (5095839041869/50000000000000 : ℝ)^3569
        have hw : |(-1695724521/10000000000 : ℝ)|=(1695724521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445740101/10000000000 : ℝ)|^4593 ≤ (2858957303969/6250000000000 : ℝ)^3569
        have hw : |(5445740101/10000000000 : ℝ)|=(5445740101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_6 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132245949/250000000 : ℝ)*x 0 + (2722869953/5000000000 : ℝ)*x 1 + (-105982813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132245949/250000000 : ℝ)^4593 ≤ (2203250168899/5000000000000 : ℝ)^3569 := by
    have hnat : (132245949 : ℕ)^4593*5000000000000^3569 ≤ 2203250168899^3569*250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132245949 250000000 2203250168899 5000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722869953/5000000000 : ℝ)^4593 ≤ (45743314755579/100000000000000 : ℝ)^3569 := by
    have hnat : (2722869953 : ℕ)^4593*100000000000000^3569 ≤ 45743314755579^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722869953 5000000000 45743314755579 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105982813/625000000 : ℝ)^4593 ≤ (1019168185051/10000000000000 : ℝ)^3569 := by
    have hnat : (105982813 : ℕ)^4593*10000000000000^3569 ≤ 1019168185051^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105982813 625000000 1019168185051 10000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132245949/250000000 : ℝ), (2722869953/5000000000 : ℝ), (-105982813/625000000 : ℝ)] ![(2203250168899/5000000000000 : ℝ), (45743314755579/100000000000000 : ℝ), (1019168185051/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132245949/250000000 : ℝ)|^4593 ≤ (2203250168899/5000000000000 : ℝ)^3569
        have hw : |(132245949/250000000 : ℝ)|=(132245949/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722869953/5000000000 : ℝ)|^4593 ≤ (45743314755579/100000000000000 : ℝ)^3569
        have hw : |(2722869953/5000000000 : ℝ)|=(2722869953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105982813/625000000 : ℝ)|^4593 ≤ (1019168185051/10000000000000 : ℝ)^3569
        have hw : |(-105982813/625000000 : ℝ)|=(105982813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s2_7 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062877543/2500000000 : ℝ)*x 0 + (2270151759/5000000000 : ℝ)*x 1 + (31825787/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062877543/2500000000 : ℝ)^4593 ≤ (3326340190407/10000000000000 : ℝ)^3569 := by
    have hnat : (1062877543 : ℕ)^4593*10000000000000^3569 ≤ 3326340190407^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062877543 2500000000 3326340190407 10000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270151759/5000000000 : ℝ)^4593 ≤ (36199065688213/100000000000000 : ℝ)^3569 := by
    have hnat : (2270151759 : ℕ)^4593*100000000000000^3569 ≤ 36199065688213^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270151759 5000000000 36199065688213 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31825787/80000000 : ℝ)^4593 ≤ (7634383098189/25000000000000 : ℝ)^3569 := by
    have hnat : (31825787 : ℕ)^4593*25000000000000^3569 ≤ 7634383098189^3569*80000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31825787 80000000 7634383098189 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062877543/2500000000 : ℝ), (2270151759/5000000000 : ℝ), (31825787/80000000 : ℝ)] ![(3326340190407/10000000000000 : ℝ), (36199065688213/100000000000000 : ℝ), (7634383098189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062877543/2500000000 : ℝ)|^4593 ≤ (3326340190407/10000000000000 : ℝ)^3569
        have hw : |(1062877543/2500000000 : ℝ)|=(1062877543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270151759/5000000000 : ℝ)|^4593 ≤ (36199065688213/100000000000000 : ℝ)^3569
        have hw : |(2270151759/5000000000 : ℝ)|=(2270151759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31825787/80000000 : ℝ)|^4593 ≤ (7634383098189/25000000000000 : ℝ)^3569
        have hw : |(31825787/80000000 : ℝ)|=(31825787/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1548_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8981/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10689/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7937/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8981/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8981/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8981/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8981/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8981/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8981/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4407/50000 : ℝ) ^ (4591/1024 : ℝ) ≤ (373095902147187/20000000000000000000 : ℝ) := by
    have hpowers : (4407/50000 : ℝ)^4591 ≤ (373095902147187/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4407 : ℕ)^4591*20000000000000000000^1024 ≤ 373095902147187^1024*50000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4407 50000 373095902147187 20000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4407/50000 : ℝ)) (X := (373095902147187/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8981/50000 : ℝ) ^ (4591/1024 : ℝ) ≤ (5673943468209027/12500000000000000000 : ℝ) := by
    have hpowers : (8981/50000 : ℝ)^4591 ≤ (5673943468209027/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8981 : ℕ)^4591*12500000000000000000^1024 ≤ 5673943468209027^1024*50000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8981 50000 5673943468209027 12500000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8981/50000 : ℝ)) (X := (5673943468209027/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000373095902147187/10000000000000000000 : ℝ) ≤ (1000008321600229/1000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (10000373095902147187/10000000000000000000 : ℝ)^1024 ≤ (1000008321600229/1000000000000000 : ℝ)^4591 := by
      have hnat : (10000373095902147187 : ℕ)^1024*1000000000000000^4591 ≤ 1000008321600229^4591*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000373095902147187 10000000000000000000 1000008321600229 1000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000008321600229/1000000000000000 : ℝ)) (X := (10000373095902147187/10000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047257027256408151/100000000000000000000 : ℝ) ≤ (2500263462832719/2500000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (100047257027256408151/100000000000000000000 : ℝ)^1024 ≤ (2500263462832719/2500000000000000 : ℝ)^4591 := by
      have hnat : (100047257027256408151 : ℕ)^1024*2500000000000000^4591 ≤ 2500263462832719^4591*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047257027256408151 100000000000000000000 2500263462832719 2500000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500263462832719/2500000000000000 : ℝ)) (X := (100047257027256408151/100000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6255673943468209027/6250000000000000000 : ℝ) ≤ (5001012243329731/5000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (6255673943468209027/6250000000000000000 : ℝ)^1024 ≤ (5001012243329731/5000000000000000 : ℝ)^4591 := by
      have hnat : (6255673943468209027 : ℕ)^1024*5000000000000000^4591 ≤ 5001012243329731^4591*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255673943468209027 6250000000000000000 5001012243329731 5000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001012243329731/5000000000000000 : ℝ)) (X := (6255673943468209027/6250000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(373095902147187/20000000000000000000 : ℝ) ≤ ((2858239090638019841/2858750000000000000 : ℝ)+2*(485317664293/457400000000000 : ℝ)*(4407/50000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (2858239090638019841/2858750000000000000 : ℝ)+2*(485317664293/457400000000000 : ℝ)*(4407/50000 : ℝ)=(1000008321600229/1000000000000000 : ℝ) by norm_num, show 1+2*(373095902147187/20000000000000000000 : ℝ)=(10000373095902147187/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5673943468209027/12500000000000000000 : ℝ)+(373095902147187/20000000000000000000 : ℝ) ≤ ((2858239090638019841/2858750000000000000 : ℝ)+(485317664293/457400000000000 : ℝ)*((8981/50000 : ℝ)+(4407/50000 : ℝ)))^(4591/1024 : ℝ) := by
    rw [show (2858239090638019841/2858750000000000000 : ℝ)+(485317664293/457400000000000 : ℝ)*((8981/50000 : ℝ)+(4407/50000 : ℝ))=(2500263462832719/2500000000000000 : ℝ) by norm_num, show 1+(5673943468209027/12500000000000000000 : ℝ)+(373095902147187/20000000000000000000 : ℝ)=(100047257027256408151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5673943468209027/12500000000000000000 : ℝ) ≤ ((2858239090638019841/2858750000000000000 : ℝ)+2*(485317664293/457400000000000 : ℝ)*(8981/50000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (2858239090638019841/2858750000000000000 : ℝ)+2*(485317664293/457400000000000 : ℝ)*(8981/50000 : ℝ)=(5001012243329731/5000000000000000 : ℝ) by norm_num, show 1+2*(5673943468209027/12500000000000000000 : ℝ)=(6255673943468209027/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2858239090638019841/2858750000000000000 : ℝ)*(X 1 0+X 2 0)+(485317664293/457400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (4407/50000 : ℝ)) (hi := (8981/50000 : ℝ)) (c := (2858239090638019841/2858750000000000000 : ℝ)) (alpha := (485317664293/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2858239090638019841/2858750000000000000 : ℝ)*(X 0 1+X 2 1)+(485317664293/457400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (4407/50000 : ℝ)) (hi := (8981/50000 : ℝ)) (c := (2858239090638019841/2858750000000000000 : ℝ)) (alpha := (485317664293/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2858239090638019841/2858750000000000000 : ℝ)*(X 0 2+X 1 2)+(485317664293/457400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (4407/50000 : ℝ)) (hi := (8981/50000 : ℝ)) (c := (2858239090638019841/2858750000000000000 : ℝ)) (alpha := (485317664293/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1813212359/10000000000 : ℝ)*X 0 0+(2723616817/5000000000 : ℝ)*X 0 1+(5202527419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354411381/10000000000 : ℝ)*X 1 0+(-969468573/5000000000 : ℝ)*X 1 1+(650315953/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677206037/5000000000 : ℝ)*X 2 0+(1300631767/2500000000 : ℝ)*X 2 1+(-1938936957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125703861/5000000000 : ℝ)*X 0 0+(3974749259/10000000000 : ℝ)*X 0 1+(4543748109/10000000000 : ℝ)*X 0 2+(2125703861/5000000000 : ℝ)*X 1 0+(3974749259/10000000000 : ℝ)*X 1 1+(4543748109/10000000000 : ℝ)*X 1 2+(2125703861/5000000000 : ℝ)*X 2 0+(3974749259/10000000000 : ℝ)*X 2 1+(4543748109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-226656993/1250000000 : ℝ)*X 0 0+(5204008421/10000000000 : ℝ)*X 0 1+(170179379/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644919057/5000000000 : ℝ)*X 1 0+(-1695724521/10000000000 : ℝ)*X 1 1+(5445740101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132245949/250000000 : ℝ)*X 2 0+(2722869953/5000000000 : ℝ)*X 2 1+(-105982813/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1062877543/2500000000 : ℝ)*X 0 0+(2270151759/5000000000 : ℝ)*X 0 1+(31825787/80000000 : ℝ)*X 0 2+(1062877543/2500000000 : ℝ)*X 1 0+(2270151759/5000000000 : ℝ)*X 1 1+(31825787/80000000 : ℝ)*X 1 2+(1062877543/2500000000 : ℝ)*X 2 0+(2270151759/5000000000 : ℝ)*X 2 1+(31825787/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (938960699444952744512956551/142937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187170277/10000000000000 : ℝ)*(base19) + (504748139/25000000000000 : ℝ)*(base23) + (262480593/100000000000000 : ℝ)*(upper3) + (102167629/50000000000000 : ℝ)*(upper4) + (245348897/100000000000000 : ℝ)*(upper5) + (2922043690099021/100000000000000 : ℝ)*(major0) + (2922043690099021/100000000000000 : ℝ)*(major1) + (2922043690099021/100000000000000 : ℝ)*(major2) + (4086556421890129/100000000000000 : ℝ)*(sp0) + (1021646030649937/25000000000000 : ℝ)*(sp1) + (2043291987654981/50000000000000 : ℝ)*(sp2) + (351497161606733/20000000000000 : ℝ)*(sp3) + (29572412389/100000000000000 : ℝ)*(sp4) + (15358894187/100000000000000 : ℝ)*(sp7) + (439375291731963/25000000000000 : ℝ)*(f.failure) + (2043292997151259/50000000000000 : ℝ)*(f.sum) + (149636016095863/22870000000000000000000000000 : ℝ)*base65 + (3837162687850881911/285875000000000000000000000000000 : ℝ)*base67 + (1716392483258506911/285875000000000000000000000000000 : ℝ)*base69 + (4222841617143131911/285875000000000000000000000000000 : ℝ)*base71 + (157835411354243/22870000000000000000000000000 : ℝ)*base73 + (231030034023131911/285875000000000000000000000000000 : ℝ)*base75 + (1813959039593131911/285875000000000000000000000000000 : ℝ)*base77 + (2461267793212506911/285875000000000000000000000000000 : ℝ)*base79 + (70224327356033/22870000000000000000000000000 : ℝ)*base81 + (11977421/1250000000000000000000 : ℝ)*base90 + (11977421/1250000000000000000000 : ℝ)*base92 + (11977421/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177902519403856797961167/22870000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1389654513/100000000000000 : ℝ)*(base19) + (575789263/50000000000000 : ℝ)*(base23) + (3449689/100000000000000 : ℝ)*(upper2) + (171831411/100000000000000 : ℝ)*(upper3) + (248902747/100000000000000 : ℝ)*(upper5) + (2957961585463103/100000000000000 : ℝ)*(major0) + (2957961585463103/100000000000000 : ℝ)*(major1) + (2957961585463103/100000000000000 : ℝ)*(major2) + (2312196141/12500000000000 : ℝ)*(sp1) + (4162953147/50000000000000 : ℝ)*(sp2) + (2068409229783701/50000000000000 : ℝ)*(sp4) + (2068399286171881/50000000000000 : ℝ)*(sp5) + (2068404491041291/50000000000000 : ℝ)*(sp6) + (1779104452063479/100000000000000 : ℝ)*(sp7) + (1779104452063479/100000000000000 : ℝ)*(f.failure) + (2068409229783701/50000000000000 : ℝ)*(f.sum) + (47588239401821/22870000000000000000000000000 : ℝ)*base66 + (345908036211295373/285875000000000000000000000000000 : ℝ)*base67 + (544814796363920373/285875000000000000000000000000000 : ℝ)*base69 + (633296073591204627/285875000000000000000000000000000 : ℝ)*base72 + (79677857538661/22870000000000000000000000000 : ℝ)*base74 + (3159577575196829627/285875000000000000000000000000000 : ℝ)*base76 + (1024777826851204627/285875000000000000000000000000000 : ℝ)*base78 + (938700997079545373/285875000000000000000000000000000 : ℝ)*base79 + (67803884497609/22870000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15452207/5000000000000000000000 : ℝ)*base89 + (15452207/5000000000000000000000 : ℝ)*base91 + (15452207/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1548_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8981/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1548_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1548_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1548_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1548_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1548_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1548_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:23.716601+00:00
-- url     : https://prove2.me/submissions/86383342-513c-4276-9dae-5a2cb7e40c4a

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
theorem support_rectangle_w1159_s0_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1886441933/10000000000 : ℝ)*x 0 + (6050409373/10000000000 : ℝ)*x 1 + (4782618553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1886441933/10000000000 : ℝ)^261 ≤ (2743212760143/25000000000000 : ℝ)^197 := by
    have hnat : (1886441933 : ℕ)^261*25000000000000^197 ≤ 2743212760143^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886441933 10000000000 2743212760143 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6050409373/10000000000 : ℝ)^261 ≤ (51391642662029/100000000000000 : ℝ)^197 := by
    have hnat : (6050409373 : ℕ)^261*100000000000000^197 ≤ 51391642662029^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6050409373 10000000000 51391642662029 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782618553/10000000000 : ℝ)^261 ≤ (37635506286329/100000000000000 : ℝ)^197 := by
    have hnat : (4782618553 : ℕ)^261*100000000000000^197 ≤ 37635506286329^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782618553 10000000000 37635506286329 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1886441933/10000000000 : ℝ), (6050409373/10000000000 : ℝ), (4782618553/10000000000 : ℝ)] ![(2743212760143/25000000000000 : ℝ), (51391642662029/100000000000000 : ℝ), (37635506286329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1886441933/10000000000 : ℝ)|^261 ≤ (2743212760143/25000000000000 : ℝ)^197
        have hw : |(-1886441933/10000000000 : ℝ)|=(1886441933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6050409373/10000000000 : ℝ)|^261 ≤ (51391642662029/100000000000000 : ℝ)^197
        have hw : |(6050409373/10000000000 : ℝ)|=(6050409373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782618553/10000000000 : ℝ)|^261 ≤ (37635506286329/100000000000000 : ℝ)^197
        have hw : |(4782618553/10000000000 : ℝ)|=(4782618553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1103167187/2000000000 : ℝ)*x 0 + (-2613523413/10000000000 : ℝ)*x 1 + (4782618543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103167187/2000000000 : ℝ)^261 ≤ (9092803616867/20000000000000 : ℝ)^197 := by
    have hnat : (1103167187 : ℕ)^261*20000000000000^197 ≤ 9092803616867^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103167187 2000000000 9092803616867 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613523413/10000000000 : ℝ)^261 ≤ (67601902883/400000000000 : ℝ)^197 := by
    have hnat : (2613523413 : ℕ)^261*400000000000^197 ≤ 67601902883^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613523413 10000000000 67601902883 400000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782618543/10000000000 : ℝ)^261 ≤ (4704438272759/12500000000000 : ℝ)^197 := by
    have hnat : (4782618543 : ℕ)^261*12500000000000^197 ≤ 4704438272759^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782618543 10000000000 4704438272759 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103167187/2000000000 : ℝ), (-2613523413/10000000000 : ℝ), (4782618543/10000000000 : ℝ)] ![(9092803616867/20000000000000 : ℝ), (67601902883/400000000000 : ℝ), (4704438272759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103167187/2000000000 : ℝ)|^261 ≤ (9092803616867/20000000000000 : ℝ)^197
        have hw : |(1103167187/2000000000 : ℝ)|=(1103167187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2613523413/10000000000 : ℝ)|^261 ≤ (67601902883/400000000000 : ℝ)^197
        have hw : |(-2613523413/10000000000 : ℝ)|=(2613523413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782618543/10000000000 : ℝ)|^261 ≤ (4704438272759/12500000000000 : ℝ)^197
        have hw : |(4782618543/10000000000 : ℝ)|=(4782618543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2757917967/5000000000 : ℝ)*x 0 + (4782618551/10000000000 : ℝ)*x 1 + (-653380851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757917967/5000000000 : ℝ)^261 ≤ (9092803614683/20000000000000 : ℝ)^197 := by
    have hnat : (2757917967 : ℕ)^261*20000000000000^197 ≤ 9092803614683^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757917967 5000000000 9092803614683 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4782618551/10000000000 : ℝ)^261 ≤ (18817753132739/50000000000000 : ℝ)^197 := by
    have hnat : (4782618551 : ℕ)^261*50000000000000^197 ≤ 18817753132739^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782618551 10000000000 18817753132739 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653380851/2500000000 : ℝ)^261 ≤ (4225118910911/25000000000000 : ℝ)^197 := by
    have hnat : (653380851 : ℕ)^261*25000000000000^197 ≤ 4225118910911^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653380851 2500000000 4225118910911 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757917967/5000000000 : ℝ), (4782618551/10000000000 : ℝ), (-653380851/2500000000 : ℝ)] ![(9092803614683/20000000000000 : ℝ), (18817753132739/50000000000000 : ℝ), (4225118910911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757917967/5000000000 : ℝ)|^261 ≤ (9092803614683/20000000000000 : ℝ)^197
        have hw : |(2757917967/5000000000 : ℝ)|=(2757917967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4782618551/10000000000 : ℝ)|^261 ≤ (18817753132739/50000000000000 : ℝ)^197
        have hw : |(4782618551/10000000000 : ℝ)|=(4782618551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-653380851/2500000000 : ℝ)|^261 ≤ (4225118910911/25000000000000 : ℝ)^197
        have hw : |(-653380851/2500000000 : ℝ)|=(653380851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (209980969/500000000 : ℝ)*x 0 + (195018997/625000000 : ℝ)*x 1 + (2825477039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209980969/500000000 : ℝ)^261 ≤ (6336230541137/20000000000000 : ℝ)^197 := by
    have hnat : (209980969 : ℕ)^261*20000000000000^197 ≤ 6336230541137^197*500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209980969 500000000 6336230541137 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195018997/625000000 : ℝ)^261 ≤ (21373472277979/100000000000000 : ℝ)^197 := by
    have hnat : (195018997 : ℕ)^261*100000000000000^197 ≤ 21373472277979^197*625000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195018997 625000000 21373472277979 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2825477039/5000000000 : ℝ)^261 ≤ (4694537499923/10000000000000 : ℝ)^197 := by
    have hnat : (2825477039 : ℕ)^261*10000000000000^197 ≤ 4694537499923^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825477039 5000000000 4694537499923 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209980969/500000000 : ℝ), (195018997/625000000 : ℝ), (2825477039/5000000000 : ℝ)] ![(6336230541137/20000000000000 : ℝ), (21373472277979/100000000000000 : ℝ), (4694537499923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209980969/500000000 : ℝ)|^261 ≤ (6336230541137/20000000000000 : ℝ)^197
        have hw : |(209980969/500000000 : ℝ)|=(209980969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195018997/625000000 : ℝ)|^261 ≤ (21373472277979/100000000000000 : ℝ)^197
        have hw : |(195018997/625000000 : ℝ)|=(195018997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2825477039/5000000000 : ℝ)|^261 ≤ (4694537499923/10000000000000 : ℝ)^197
        have hw : |(2825477039/5000000000 : ℝ)|=(2825477039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-75661507/400000000 : ℝ)*x 0 + (4815315311/10000000000 : ℝ)*x 1 + (3008280893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75661507/400000000 : ℝ)^261 ≤ (1101213797637/10000000000000 : ℝ)^197 := by
    have hnat : (75661507 : ℕ)^261*10000000000000^197 ≤ 1101213797637^197*400000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75661507 400000000 1101213797637 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815315311/10000000000 : ℝ)^261 ≤ (9494192924721/25000000000000 : ℝ)^197 := by
    have hnat : (4815315311 : ℕ)^261*25000000000000^197 ≤ 9494192924721^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815315311 10000000000 9494192924721 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008280893/5000000000 : ℝ)^261 ≤ (51011090313189/100000000000000 : ℝ)^197 := by
    have hnat : (3008280893 : ℕ)^261*100000000000000^197 ≤ 51011090313189^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008280893 5000000000 51011090313189 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75661507/400000000 : ℝ), (4815315311/10000000000 : ℝ), (3008280893/5000000000 : ℝ)] ![(1101213797637/10000000000000 : ℝ), (9494192924721/25000000000000 : ℝ), (51011090313189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75661507/400000000 : ℝ)|^261 ≤ (1101213797637/10000000000000 : ℝ)^197
        have hw : |(-75661507/400000000 : ℝ)|=(75661507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815315311/10000000000 : ℝ)|^261 ≤ (9494192924721/25000000000000 : ℝ)^197
        have hw : |(4815315311/10000000000 : ℝ)|=(4815315311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008280893/5000000000 : ℝ)|^261 ≤ (51011090313189/100000000000000 : ℝ)^197
        have hw : |(3008280893/5000000000 : ℝ)|=(3008280893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1292816597/2500000000 : ℝ)*x 0 + (-8622377/62500000 : ℝ)*x 1 + (601656159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292816597/2500000000 : ℝ)^261 ≤ (20869990718861/50000000000000 : ℝ)^197 := by
    have hnat : (1292816597 : ℕ)^261*50000000000000^197 ≤ 20869990718861^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292816597 2500000000 20869990718861 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8622377/62500000 : ℝ)^261 ≤ (1812232606529/25000000000000 : ℝ)^197 := by
    have hnat : (8622377 : ℕ)^261*25000000000000^197 ≤ 1812232606529^197*62500000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8622377 62500000 1812232606529 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601656159/1000000000 : ℝ)^261 ≤ (51011088111547/100000000000000 : ℝ)^197 := by
    have hnat : (601656159 : ℕ)^261*100000000000000^197 ≤ 51011088111547^197*1000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601656159 1000000000 51011088111547 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292816597/2500000000 : ℝ), (-8622377/62500000 : ℝ), (601656159/1000000000 : ℝ)] ![(20869990718861/50000000000000 : ℝ), (1812232606529/25000000000000 : ℝ), (51011088111547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292816597/2500000000 : ℝ)|^261 ≤ (20869990718861/50000000000000 : ℝ)^197
        have hw : |(1292816597/2500000000 : ℝ)|=(1292816597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8622377/62500000 : ℝ)|^261 ≤ (1812232606529/25000000000000 : ℝ)^197
        have hw : |(-8622377/62500000 : ℝ)|=(8622377/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601656159/1000000000 : ℝ)|^261 ≤ (51011088111547/100000000000000 : ℝ)^197
        have hw : |(601656159/1000000000 : ℝ)|=(601656159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1292816591/2500000000 : ℝ)*x 0 + (3008280831/5000000000 : ℝ)*x 1 + (-689790121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292816591/2500000000 : ℝ)^261 ≤ (2608748823817/6250000000000 : ℝ)^197 := by
    have hnat : (1292816591 : ℕ)^261*6250000000000^197 ≤ 2608748823817^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292816591 2500000000 2608748823817 6250000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008280831/5000000000 : ℝ)^261 ≤ (25505544460157/50000000000000 : ℝ)^197 := by
    have hnat : (3008280831 : ℕ)^261*50000000000000^197 ≤ 25505544460157^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008280831 5000000000 25505544460157 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689790121/5000000000 : ℝ)^261 ≤ (7248929883121/100000000000000 : ℝ)^197 := by
    have hnat : (689790121 : ℕ)^261*100000000000000^197 ≤ 7248929883121^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689790121 5000000000 7248929883121 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292816591/2500000000 : ℝ), (3008280831/5000000000 : ℝ), (-689790121/5000000000 : ℝ)] ![(2608748823817/6250000000000 : ℝ), (25505544460157/50000000000000 : ℝ), (7248929883121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292816591/2500000000 : ℝ)|^261 ≤ (2608748823817/6250000000000 : ℝ)^197
        have hw : |(1292816591/2500000000 : ℝ)|=(1292816591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008280831/5000000000 : ℝ)|^261 ≤ (25505544460157/50000000000000 : ℝ)^197
        have hw : |(3008280831/5000000000 : ℝ)|=(3008280831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-689790121/5000000000 : ℝ)|^261 ≤ (7248929883121/100000000000000 : ℝ)^197
        have hw : |(-689790121/5000000000 : ℝ)|=(689790121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s0_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4209791237/10000000000 : ℝ)*x 0 + (5585687479/10000000000 : ℝ)*x 1 + (3187867713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209791237/10000000000 : ℝ)^261 ≤ (15891428151137/50000000000000 : ℝ)^197 := by
    have hnat : (4209791237 : ℕ)^261*50000000000000^197 ≤ 15891428151137^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209791237 10000000000 15891428151137 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5585687479/10000000000 : ℝ)^261 ≤ (46228375872593/100000000000000 : ℝ)^197 := by
    have hnat : (5585687479 : ℕ)^261*100000000000000^197 ≤ 46228375872593^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585687479 10000000000 46228375872593 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187867713/10000000000 : ℝ)^261 ≤ (21988767810263/100000000000000 : ℝ)^197 := by
    have hnat : (3187867713 : ℕ)^261*100000000000000^197 ≤ 21988767810263^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187867713 10000000000 21988767810263 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209791237/10000000000 : ℝ), (5585687479/10000000000 : ℝ), (3187867713/10000000000 : ℝ)] ![(15891428151137/50000000000000 : ℝ), (46228375872593/100000000000000 : ℝ), (21988767810263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209791237/10000000000 : ℝ)|^261 ≤ (15891428151137/50000000000000 : ℝ)^197
        have hw : |(4209791237/10000000000 : ℝ)|=(4209791237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5585687479/10000000000 : ℝ)|^261 ≤ (46228375872593/100000000000000 : ℝ)^197
        have hw : |(5585687479/10000000000 : ℝ)|=(5585687479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187867713/10000000000 : ℝ)|^261 ≤ (21988767810263/100000000000000 : ℝ)^197
        have hw : |(3187867713/10000000000 : ℝ)|=(3187867713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (483/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (111/400 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8351/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8351 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8351*1^2048 ≤ 0^2048*1^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8351/2048 : ℝ) ≤ (476842772520788477/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8351 ≤ (476842772520788477/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8351*20000000000000000000^2048 ≤ 476842772520788477^2048*5^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 476842772520788477 20000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (476842772520788477/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8351 := by
      have hnat : (1 : ℕ)^2048*1^8351 ≤ 1^8351*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20476842772520788477/20000000000000000000 : ℝ) ≤ (5028975805016259/5000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (20476842772520788477/20000000000000000000 : ℝ)^2048 ≤ (5028975805016259/5000000000000000 : ℝ)^8351 := by
      have hnat : (20476842772520788477 : ℕ)^2048*5000000000000000^8351 ≤ 5028975805016259^8351*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20476842772520788477 20000000000000000000 5028975805016259 5000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028975805016259/5000000000000000 : ℝ)) (X := (20476842772520788477/20000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10476842772520788477/10000000000000000000 : ℝ) ≤ (2528975805016259/2500000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (10476842772520788477/10000000000000000000 : ℝ)^2048 ≤ (2528975805016259/2500000000000000 : ℝ)^8351 := by
      have hnat : (10476842772520788477 : ℕ)^2048*2500000000000000^8351 ≤ 2528975805016259^8351*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10476842772520788477 10000000000000000000 2528975805016259 2500000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528975805016259/2500000000000000 : ℝ)) (X := (10476842772520788477/10000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28975805016259/2000000000000000 : ℝ)*(0 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28975805016259/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(476842772520788477/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28975805016259/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28975805016259/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028975805016259/5000000000000000 : ℝ) by norm_num, show 1+(476842772520788477/20000000000000000000 : ℝ)+(0 : ℝ)=(20476842772520788477/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(476842772520788477/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28975805016259/2000000000000000 : ℝ)*(2/5 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28975805016259/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528975805016259/2500000000000000 : ℝ) by norm_num, show 1+2*(476842772520788477/20000000000000000000 : ℝ)=(10476842772520788477/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28975805016259/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28975805016259/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28975805016259/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28975805016259/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28975805016259/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28975805016259/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1886441933/10000000000 : ℝ)*X 0 0+(6050409373/10000000000 : ℝ)*X 0 1+(4782618553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103167187/2000000000 : ℝ)*X 1 0+(-2613523413/10000000000 : ℝ)*X 1 1+(4782618543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757917967/5000000000 : ℝ)*X 2 0+(4782618551/10000000000 : ℝ)*X 2 1+(-653380851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209980969/500000000 : ℝ)*X 0 0+(195018997/625000000 : ℝ)*X 0 1+(2825477039/5000000000 : ℝ)*X 0 2+(209980969/500000000 : ℝ)*X 1 0+(195018997/625000000 : ℝ)*X 1 1+(2825477039/5000000000 : ℝ)*X 1 2+(209980969/500000000 : ℝ)*X 2 0+(195018997/625000000 : ℝ)*X 2 1+(2825477039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-75661507/400000000 : ℝ)*X 0 0+(4815315311/10000000000 : ℝ)*X 0 1+(3008280893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292816597/2500000000 : ℝ)*X 1 0+(-8622377/62500000 : ℝ)*X 1 1+(601656159/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292816591/2500000000 : ℝ)*X 2 0+(3008280831/5000000000 : ℝ)*X 2 1+(-689790121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209791237/10000000000 : ℝ)*X 0 0+(5585687479/10000000000 : ℝ)*X 0 1+(3187867713/10000000000 : ℝ)*X 0 2+(4209791237/10000000000 : ℝ)*X 1 0+(5585687479/10000000000 : ℝ)*X 1 1+(3187867713/10000000000 : ℝ)*X 1 2+(4209791237/10000000000 : ℝ)*X 2 0+(5585687479/10000000000 : ℝ)*X 2 1+(3187867713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6260462812369912029/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16476827/25000000000000 : ℝ)*(base1) + (24081923/1562500000000 : ℝ)*(base19) + (35860981/2500000000000 : ℝ)*(base23) + (106660829/100000000000000 : ℝ)*(base24) + (353487859/100000000000000 : ℝ)*(upper3) + (591971043280157/100000000000000 : ℝ)*(major0) + (591971043280157/100000000000000 : ℝ)*(major1) + (591971043280157/100000000000000 : ℝ)*(major2) + (394389409707187/50000000000000 : ℝ)*(sp0) + (788780602433807/100000000000000 : ℝ)*(sp1) + (78878060257681/10000000000000 : ℝ)*(sp2) + (15806278468107/4000000000000 : ℝ)*(sp3) + (1695084907/50000000000000 : ℝ)*(sp4) + (676647837/25000000000000 : ℝ)*(sp7) + (395159734201331/100000000000000 : ℝ)*(f.failure) + (9859776795961/1250000000000 : ℝ)*(f.sum) + (76503081327337/100000000000000000000000000000 : ℝ)*base66 + (884883487472663/200000000000000000000000000000 : ℝ)*base67 + (378891197072663/200000000000000000000000000000 : ℝ)*base69 + (889251372872663/200000000000000000000000000000 : ℝ)*base71 + (89963923027337/100000000000000000000000000000 : ℝ)*base74 + (1651316282072663/200000000000000000000000000000 : ℝ)*base75 + (792524173872663/200000000000000000000000000000 : ℝ)*base77 + (1916152956672663/200000000000000000000000000000 : ℝ)*base79 + (357850376327337/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (69470183/10000000000000000000000 : ℝ)*base90 + (69470183/10000000000000000000000 : ℝ)*base92 + (69470183/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498888235993035814662621/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1609493/2500000000000 : ℝ)*(base1) + (619213289/50000000000000 : ℝ)*(base19) + (1234578463/100000000000000 : ℝ)*(base23) + (130967731/100000000000000 : ℝ)*(upper3) + (74122419/50000000000000 : ℝ)*(upper5) + (624757186745227/100000000000000 : ℝ)*(major0) + (624757186745227/100000000000000 : ℝ)*(major1) + (624757186745227/100000000000000 : ℝ)*(major2) + (38912481/1562500000000 : ℝ)*(sp1) + (2490629601/100000000000000 : ℝ)*(sp2) + (208117182705389/25000000000000 : ℝ)*(sp4) + (832464937616473/100000000000000 : ℝ)*(sp5) + (832464941233771/100000000000000 : ℝ)*(sp6) + (83409095274563/20000000000000 : ℝ)*(sp7) + (83409108150507/20000000000000 : ℝ)*(f.failure) + (166493733288367/20000000000000 : ℝ)*(f.sum) + (183742040145793/100000000000000000000000000000 : ℝ)*base65 + (850093434554207/200000000000000000000000000000 : ℝ)*base68 + (491484196554207/200000000000000000000000000000 : ℝ)*base70 + (1002574918154207/200000000000000000000000000000 : ℝ)*base72 + (256117802345793/100000000000000000000000000000 : ℝ)*base73 + (66222850245793/200000000000000000000000000000 : ℝ)*base75 + (839684600954207/200000000000000000000000000000 : ℝ)*base78 + (205087761954207/200000000000000000000000000000 : ℝ)*base80 + (528733254745793/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6557951/2000000000000000000000 : ℝ)*base90 + (6557951/2000000000000000000000 : ℝ)*base92 + (6557951/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1159_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (111/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1159_s1_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-83595077/400000000 : ℝ)*x 0 + (142424741/250000000 : ℝ)*x 1 + (1251451333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83595077/400000000 : ℝ)^261 ≤ (2513484530097/20000000000000 : ℝ)^197 := by
    have hnat : (83595077 : ℕ)^261*20000000000000^197 ≤ 2513484530097^197*400000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83595077 400000000 2513484530097 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142424741/250000000 : ℝ)^261 ≤ (5931591263023/12500000000000 : ℝ)^197 := by
    have hnat : (142424741 : ℕ)^261*12500000000000^197 ≤ 5931591263023^197*250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142424741 250000000 5931591263023 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251451333/2500000000 : ℝ)^261 ≤ (7995969445959/20000000000000 : ℝ)^197 := by
    have hnat : (1251451333 : ℕ)^261*20000000000000^197 ≤ 7995969445959^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251451333 2500000000 7995969445959 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83595077/400000000 : ℝ), (142424741/250000000 : ℝ), (1251451333/2500000000 : ℝ)] ![(2513484530097/20000000000000 : ℝ), (5931591263023/12500000000000 : ℝ), (7995969445959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83595077/400000000 : ℝ)|^261 ≤ (2513484530097/20000000000000 : ℝ)^197
        have hw : |(-83595077/400000000 : ℝ)|=(83595077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142424741/250000000 : ℝ)|^261 ≤ (5931591263023/12500000000000 : ℝ)^197
        have hw : |(142424741/250000000 : ℝ)|=(142424741/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251451333/2500000000 : ℝ)|^261 ≤ (7995969445959/20000000000000 : ℝ)^197
        have hw : |(1251451333/2500000000 : ℝ)|=(1251451333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5418189283/10000000000 : ℝ)*x 0 + (-492511333/2000000000 : ℝ)*x 1 + (2502902199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418189283/10000000000 : ℝ)^261 ≤ (8880155068227/20000000000000 : ℝ)^197 := by
    have hnat : (5418189283 : ℕ)^261*20000000000000^197 ≤ 8880155068227^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418189283 10000000000 8880155068227 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492511333/2000000000 : ℝ)^261 ≤ (3904846822253/25000000000000 : ℝ)^197 := by
    have hnat : (492511333 : ℕ)^261*25000000000000^197 ≤ 3904846822253^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492511333 2000000000 3904846822253 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502902199/5000000000 : ℝ)^261 ≤ (19989918673403/50000000000000 : ℝ)^197 := by
    have hnat : (2502902199 : ℕ)^261*50000000000000^197 ≤ 19989918673403^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502902199 5000000000 19989918673403 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418189283/10000000000 : ℝ), (-492511333/2000000000 : ℝ), (2502902199/5000000000 : ℝ)] ![(8880155068227/20000000000000 : ℝ), (3904846822253/25000000000000 : ℝ), (19989918673403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418189283/10000000000 : ℝ)|^261 ≤ (8880155068227/20000000000000 : ℝ)^197
        have hw : |(5418189283/10000000000 : ℝ)|=(5418189283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492511333/2000000000 : ℝ)|^261 ≤ (3904846822253/25000000000000 : ℝ)^197
        have hw : |(-492511333/2000000000 : ℝ)|=(492511333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502902199/5000000000 : ℝ)|^261 ≤ (19989918673403/50000000000000 : ℝ)^197
        have hw : |(2502902199/5000000000 : ℝ)|=(2502902199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (677273923/1250000000 : ℝ)*x 0 + (2502901249/5000000000 : ℝ)*x 1 + (-307819543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677273923/1250000000 : ℝ)^261 ≤ (44400798151737/100000000000000 : ℝ)^197 := by
    have hnat : (677273923 : ℕ)^261*100000000000000^197 ≤ 44400798151737^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677273923 1250000000 44400798151737 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502901249/5000000000 : ℝ)^261 ≤ (19989908621113/50000000000000 : ℝ)^197 := by
    have hnat : (2502901249 : ℕ)^261*50000000000000^197 ≤ 19989908621113^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502901249 5000000000 19989908621113 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307819543/1250000000 : ℝ)^261 ≤ (780969229577/5000000000000 : ℝ)^197 := by
    have hnat : (307819543 : ℕ)^261*5000000000000^197 ≤ 780969229577^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307819543 1250000000 780969229577 5000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677273923/1250000000 : ℝ), (2502901249/5000000000 : ℝ), (-307819543/1250000000 : ℝ)] ![(44400798151737/100000000000000 : ℝ), (19989908621113/50000000000000 : ℝ), (780969229577/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677273923/1250000000 : ℝ)|^261 ≤ (44400798151737/100000000000000 : ℝ)^197
        have hw : |(677273923/1250000000 : ℝ)|=(677273923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502901249/5000000000 : ℝ)|^261 ≤ (19989908621113/50000000000000 : ℝ)^197
        have hw : |(2502901249/5000000000 : ℝ)|=(2502901249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307819543/1250000000 : ℝ)|^261 ≤ (780969229577/5000000000000 : ℝ)^197
        have hw : |(-307819543/1250000000 : ℝ)|=(307819543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2157997919/5000000000 : ℝ)*x 0 + (920054869/2500000000 : ℝ)*x 1 + (505989529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157997919/5000000000 : ℝ)^261 ≤ (513273311919/1562500000000 : ℝ)^197 := by
    have hnat : (2157997919 : ℕ)^261*1562500000000^197 ≤ 513273311919^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157997919 5000000000 513273311919 1562500000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920054869/2500000000 : ℝ)^261 ≤ (1329865668749/5000000000000 : ℝ)^197 := by
    have hnat : (920054869 : ℕ)^261*5000000000000^197 ≤ 1329865668749^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920054869 2500000000 1329865668749 5000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505989529/1000000000 : ℝ)^261 ≤ (40553194649371/100000000000000 : ℝ)^197 := by
    have hnat : (505989529 : ℕ)^261*100000000000000^197 ≤ 40553194649371^197*1000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505989529 1000000000 40553194649371 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157997919/5000000000 : ℝ), (920054869/2500000000 : ℝ), (505989529/1000000000 : ℝ)] ![(513273311919/1562500000000 : ℝ), (1329865668749/5000000000000 : ℝ), (40553194649371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157997919/5000000000 : ℝ)|^261 ≤ (513273311919/1562500000000 : ℝ)^197
        have hw : |(2157997919/5000000000 : ℝ)|=(2157997919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(920054869/2500000000 : ℝ)|^261 ≤ (1329865668749/5000000000000 : ℝ)^197
        have hw : |(920054869/2500000000 : ℝ)|=(920054869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505989529/1000000000 : ℝ)|^261 ≤ (40553194649371/100000000000000 : ℝ)^197
        have hw : |(505989529/1000000000 : ℝ)|=(505989529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-522666029/2500000000 : ℝ)*x 0 + (1003036367/2000000000 : ℝ)*x 1 + (568742527/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522666029/2500000000 : ℝ)^261 ≤ (3143423664177/25000000000000 : ℝ)^197 := by
    have hnat : (522666029 : ℕ)^261*25000000000000^197 ≤ 3143423664177^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522666029 2500000000 3143423664177 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003036367/2000000000 : ℝ)^261 ≤ (8015818710139/20000000000000 : ℝ)^197 := by
    have hnat : (1003036367 : ℕ)^261*20000000000000^197 ≤ 8015818710139^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003036367 2000000000 8015818710139 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568742527/1000000000 : ℝ)^261 ≤ (23673605884781/50000000000000 : ℝ)^197 := by
    have hnat : (568742527 : ℕ)^261*50000000000000^197 ≤ 23673605884781^197*1000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568742527 1000000000 23673605884781 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522666029/2500000000 : ℝ), (1003036367/2000000000 : ℝ), (568742527/1000000000 : ℝ)] ![(3143423664177/25000000000000 : ℝ), (8015818710139/20000000000000 : ℝ), (23673605884781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522666029/2500000000 : ℝ)|^261 ≤ (3143423664177/25000000000000 : ℝ)^197
        have hw : |(-522666029/2500000000 : ℝ)|=(522666029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003036367/2000000000 : ℝ)|^261 ≤ (8015818710139/20000000000000 : ℝ)^197
        have hw : |(1003036367/2000000000 : ℝ)|=(1003036367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568742527/1000000000 : ℝ)|^261 ≤ (23673605884781/50000000000000 : ℝ)^197
        have hw : |(568742527/1000000000 : ℝ)|=(568742527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2620415871/5000000000 : ℝ)*x 0 + (-890466033/5000000000 : ℝ)*x 1 + (5687428701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620415871/5000000000 : ℝ)^261 ≤ (21242757956941/50000000000000 : ℝ)^197 := by
    have hnat : (2620415871 : ℕ)^261*50000000000000^197 ≤ 21242757956941^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620415871 5000000000 21242757956941 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890466033/5000000000 : ℝ)^261 ≤ (10167234466723/100000000000000 : ℝ)^197 := by
    have hnat : (890466033 : ℕ)^261*100000000000000^197 ≤ 10167234466723^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890466033 5000000000 10167234466723 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5687428701/10000000000 : ℝ)^261 ≤ (47347249611533/100000000000000 : ℝ)^197 := by
    have hnat : (5687428701 : ℕ)^261*100000000000000^197 ≤ 47347249611533^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687428701 10000000000 47347249611533 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620415871/5000000000 : ℝ), (-890466033/5000000000 : ℝ), (5687428701/10000000000 : ℝ)] ![(21242757956941/50000000000000 : ℝ), (10167234466723/100000000000000 : ℝ), (47347249611533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620415871/5000000000 : ℝ)|^261 ≤ (21242757956941/50000000000000 : ℝ)^197
        have hw : |(2620415871/5000000000 : ℝ)|=(2620415871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890466033/5000000000 : ℝ)|^261 ≤ (10167234466723/100000000000000 : ℝ)^197
        have hw : |(-890466033/5000000000 : ℝ)|=(890466033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5687428701/10000000000 : ℝ)|^261 ≤ (47347249611533/100000000000000 : ℝ)^197
        have hw : |(5687428701/10000000000 : ℝ)|=(5687428701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (327551919/625000000 : ℝ)*x 0 + (5687430241/10000000000 : ℝ)*x 1 + (-890465647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327551919/625000000 : ℝ)^261 ≤ (42485504765489/100000000000000 : ℝ)^197 := by
    have hnat : (327551919 : ℕ)^261*100000000000000^197 ≤ 42485504765489^197*625000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327551919 625000000 42485504765489 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687430241/10000000000 : ℝ)^261 ≤ (5918408324607/12500000000000 : ℝ)^197 := by
    have hnat : (5687430241 : ℕ)^261*12500000000000^197 ≤ 5918408324607^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687430241 10000000000 5918408324607 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890465647/5000000000 : ℝ)^261 ≤ (1270903578451/12500000000000 : ℝ)^197 := by
    have hnat : (890465647 : ℕ)^261*12500000000000^197 ≤ 1270903578451^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890465647 5000000000 1270903578451 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327551919/625000000 : ℝ), (5687430241/10000000000 : ℝ), (-890465647/5000000000 : ℝ)] ![(42485504765489/100000000000000 : ℝ), (5918408324607/12500000000000 : ℝ), (1270903578451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327551919/625000000 : ℝ)|^261 ≤ (42485504765489/100000000000000 : ℝ)^197
        have hw : |(327551919/625000000 : ℝ)|=(327551919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687430241/10000000000 : ℝ)|^261 ≤ (5918408324607/12500000000000 : ℝ)^197
        have hw : |(5687430241/10000000000 : ℝ)|=(5687430241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890465647/5000000000 : ℝ)|^261 ≤ (1270903578451/12500000000000 : ℝ)^197
        have hw : |(-890465647/5000000000 : ℝ)|=(890465647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s1_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4317555541/10000000000 : ℝ)*x 0 + (2520590287/5000000000 : ℝ)*x 1 + (1849651157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317555541/10000000000 : ℝ)^261 ≤ (32865220535711/100000000000000 : ℝ)^197 := by
    have hnat : (4317555541 : ℕ)^261*100000000000000^197 ≤ 32865220535711^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317555541 10000000000 32865220535711 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2520590287/5000000000 : ℝ)^261 ≤ (40354594373573/100000000000000 : ℝ)^197 := by
    have hnat : (2520590287 : ℕ)^261*100000000000000^197 ≤ 40354594373573^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520590287 5000000000 40354594373573 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1849651157/5000000000 : ℝ)^261 ≤ (13390092539279/50000000000000 : ℝ)^197 := by
    have hnat : (1849651157 : ℕ)^261*50000000000000^197 ≤ 13390092539279^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849651157 5000000000 13390092539279 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317555541/10000000000 : ℝ), (2520590287/5000000000 : ℝ), (1849651157/5000000000 : ℝ)] ![(32865220535711/100000000000000 : ℝ), (40354594373573/100000000000000 : ℝ), (13390092539279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317555541/10000000000 : ℝ)|^261 ≤ (32865220535711/100000000000000 : ℝ)^197
        have hw : |(4317555541/10000000000 : ℝ)|=(4317555541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2520590287/5000000000 : ℝ)|^261 ≤ (40354594373573/100000000000000 : ℝ)^197
        have hw : |(2520590287/5000000000 : ℝ)|=(2520590287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1849651157/5000000000 : ℝ)|^261 ≤ (13390092539279/50000000000000 : ℝ)^197
        have hw : |(1849651157/5000000000 : ℝ)|=(1849651157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (111/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (359/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20361/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (111/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (111/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (111/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (111/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (111/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (111/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (483/100000 : ℝ) ^ (8351/2048 : ℝ) ≤ (17986546389/50000000000000000000 : ℝ) := by
    have hpowers : (483/100000 : ℝ)^8351 ≤ (17986546389/50000000000000000000 : ℝ)^2048 := by
      have hnat : (483 : ℕ)^8351*50000000000000000000^2048 ≤ 17986546389^2048*100000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        483 100000 17986546389 50000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (483/100000 : ℝ)) (X := (17986546389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (111/400 : ℝ) ^ (8351/2048 : ℝ) ≤ (268410016839929973/50000000000000000000 : ℝ) := by
    have hpowers : (111/400 : ℝ)^8351 ≤ (268410016839929973/50000000000000000000 : ℝ)^2048 := by
      have hnat : (111 : ℕ)^8351*50000000000000000000^2048 ≤ 268410016839929973^2048*400^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111 400 268410016839929973 50000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (111/400 : ℝ)) (X := (268410016839929973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000017986546389/25000000000000000000 : ℝ) ≤ (10000000001764409/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (25000000017986546389/25000000000000000000 : ℝ)^2048 ≤ (10000000001764409/10000000000000000 : ℝ)^8351 := by
      have hnat : (25000000017986546389 : ℕ)^2048*10000000000000000^8351 ≤ 10000000001764409^8351*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000017986546389 25000000000000000000 10000000001764409 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001764409/10000000000000000 : ℝ)) (X := (25000000017986546389/25000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25134205017413238181/25000000000000000000 : ℝ) ≤ (5006569196708127/5000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (25134205017413238181/25000000000000000000 : ℝ)^2048 ≤ (5006569196708127/5000000000000000 : ℝ)^8351 := by
      have hnat : (25134205017413238181 : ℕ)^2048*5000000000000000^8351 ≤ 5006569196708127^8351*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25134205017413238181 25000000000000000000 5006569196708127 5000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006569196708127/5000000000000000 : ℝ)) (X := (25134205017413238181/25000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25268410016839929973/25000000000000000000 : ℝ) ≤ (10026276785068099/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (25268410016839929973/25000000000000000000 : ℝ)^2048 ≤ (10026276785068099/10000000000000000 : ℝ)^8351 := by
      have hnat : (25268410016839929973 : ℕ)^2048*10000000000000000^8351 ≤ 10026276785068099^8351*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25268410016839929973 25000000000000000000 10026276785068099 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026276785068099/10000000000000000 : ℝ)) (X := (25268410016839929973/25000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17986546389/50000000000000000000 : ℝ) ≤ ((90885769453924819311/90890000000000000000 : ℝ)+2*(2627678330369/545340000000000 : ℝ)*(483/100000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (90885769453924819311/90890000000000000000 : ℝ)+2*(2627678330369/545340000000000 : ℝ)*(483/100000 : ℝ)=(10000000001764409/10000000000000000 : ℝ) by norm_num, show 1+2*(17986546389/50000000000000000000 : ℝ)=(25000000017986546389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(268410016839929973/50000000000000000000 : ℝ)+(17986546389/50000000000000000000 : ℝ) ≤ ((90885769453924819311/90890000000000000000 : ℝ)+(2627678330369/545340000000000 : ℝ)*((111/400 : ℝ)+(483/100000 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (90885769453924819311/90890000000000000000 : ℝ)+(2627678330369/545340000000000 : ℝ)*((111/400 : ℝ)+(483/100000 : ℝ))=(5006569196708127/5000000000000000 : ℝ) by norm_num, show 1+(268410016839929973/50000000000000000000 : ℝ)+(17986546389/50000000000000000000 : ℝ)=(25134205017413238181/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(268410016839929973/50000000000000000000 : ℝ) ≤ ((90885769453924819311/90890000000000000000 : ℝ)+2*(2627678330369/545340000000000 : ℝ)*(111/400 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (90885769453924819311/90890000000000000000 : ℝ)+2*(2627678330369/545340000000000 : ℝ)*(111/400 : ℝ)=(10026276785068099/10000000000000000 : ℝ) by norm_num, show 1+2*(268410016839929973/50000000000000000000 : ℝ)=(25268410016839929973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (90885769453924819311/90890000000000000000 : ℝ)*(X 1 0+X 2 0)+(2627678330369/545340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (483/100000 : ℝ)) (hi := (111/400 : ℝ)) (c := (90885769453924819311/90890000000000000000 : ℝ)) (alpha := (2627678330369/545340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (90885769453924819311/90890000000000000000 : ℝ)*(X 0 1+X 2 1)+(2627678330369/545340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (483/100000 : ℝ)) (hi := (111/400 : ℝ)) (c := (90885769453924819311/90890000000000000000 : ℝ)) (alpha := (2627678330369/545340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (90885769453924819311/90890000000000000000 : ℝ)*(X 0 2+X 1 2)+(2627678330369/545340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (483/100000 : ℝ)) (hi := (111/400 : ℝ)) (c := (90885769453924819311/90890000000000000000 : ℝ)) (alpha := (2627678330369/545340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-83595077/400000000 : ℝ)*X 0 0+(142424741/250000000 : ℝ)*X 0 1+(1251451333/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5418189283/10000000000 : ℝ)*X 1 0+(-492511333/2000000000 : ℝ)*X 1 1+(2502902199/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677273923/1250000000 : ℝ)*X 2 0+(2502901249/5000000000 : ℝ)*X 2 1+(-307819543/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157997919/5000000000 : ℝ)*X 0 0+(920054869/2500000000 : ℝ)*X 0 1+(505989529/1000000000 : ℝ)*X 0 2+(2157997919/5000000000 : ℝ)*X 1 0+(920054869/2500000000 : ℝ)*X 1 1+(505989529/1000000000 : ℝ)*X 1 2+(2157997919/5000000000 : ℝ)*X 2 0+(920054869/2500000000 : ℝ)*X 2 1+(505989529/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-522666029/2500000000 : ℝ)*X 0 0+(1003036367/2000000000 : ℝ)*X 0 1+(568742527/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2620415871/5000000000 : ℝ)*X 1 0+(-890466033/5000000000 : ℝ)*X 1 1+(5687428701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327551919/625000000 : ℝ)*X 2 0+(5687430241/10000000000 : ℝ)*X 2 1+(-890465647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317555541/10000000000 : ℝ)*X 0 0+(2520590287/5000000000 : ℝ)*X 0 1+(1849651157/5000000000 : ℝ)*X 0 2+(4317555541/10000000000 : ℝ)*X 1 0+(2520590287/5000000000 : ℝ)*X 1 1+(1849651157/5000000000 : ℝ)*X 1 2+(4317555541/10000000000 : ℝ)*X 2 0+(2520590287/5000000000 : ℝ)*X 2 1+(1849651157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5300208990420330895573976267/908900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125017029/20000000000000 : ℝ)*(base1) + (914680151/100000000000000 : ℝ)*(base19) + (771847589/50000000000000 : ℝ)*(base23) + (46886867/25000000000000 : ℝ)*(base37) + (29471153/50000000000000 : ℝ)*(upper3) + (217160023639133/20000000000000 : ℝ)*(major0) + (217160023639133/20000000000000 : ℝ)*(major1) + (217160023639133/20000000000000 : ℝ)*(major2) + (723396390876509/50000000000000 : ℝ)*(sp0) + (361697626493331/25000000000000 : ℝ)*(sp1) + (144679195418931/10000000000000 : ℝ)*(sp2) + (724805731492407/100000000000000 : ℝ)*(sp3) + (167652077/12500000000000 : ℝ)*(sp4) + (2077231013/100000000000000 : ℝ)*(sp5) + (36240327206251/5000000000000 : ℝ)*(f.failure) + (1446793497884489/100000000000000 : ℝ)*(f.sum) + (7471767418813/5453400000000000000000000000 : ℝ)*base65 + (23964300180161207911/5453400000000000000000000000000000 : ℝ)*base68 + (31916550115088807911/5453400000000000000000000000000000 : ℝ)*base70 + (5056712291254007911/5453400000000000000000000000000000 : ℝ)*base72 + (17137274155153/27267000000000000000000000000 : ℝ)*base74 + (22643614762353407911/5453400000000000000000000000000000 : ℝ)*base76 + (16885157079740807911/5453400000000000000000000000000000 : ℝ)*base78 + (50009599661207911/5453400000000000000000000000000000 : ℝ)*base80 + (4599003168749/5453400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (375743/500000000000000000000 : ℝ)*base90 + (375743/500000000000000000000 : ℝ)*base92 + (375743/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4631262622359589597385889297/1136125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338332311/12500000000000 : ℝ)*(base19) + (670836981/20000000000000 : ℝ)*(base23) + (384047109/100000000000000 : ℝ)*(upper2) + (661921097/100000000000000 : ℝ)*(upper3) + (9233827/2500000000000 : ℝ)*(upper5) + (279096962238691/25000000000000 : ℝ)*(major0) + (279096962238691/25000000000000 : ℝ)*(major1) + (279096962238691/25000000000000 : ℝ)*(major2) + (7450756391/50000000000000 : ℝ)*(sp1) + (21087400819/100000000000000 : ℝ)*(sp2) + (185943840328689/12500000000000 : ℝ)*(sp4) + (743766557229121/50000000000000 : ℝ)*(sp5) + (371881570260947/25000000000000 : ℝ)*(sp6) + (745224839401107/100000000000000 : ℝ)*(sp7) + (745224839401107/100000000000000 : ℝ)*(f.failure) + (185943840328689/12500000000000 : ℝ)*(f.sum) + (166105089733249/27267000000000000000000000000 : ℝ)*base66 + (62617041565312485703/6816750000000000000000000000000000 : ℝ)*base67 + (41307745411987485703/6816750000000000000000000000000000 : ℝ)*base69 + (38031704531894235703/6816750000000000000000000000000000 : ℝ)*base71 + (3090183805039/6816750000000000000000000000 : ℝ)*base74 + (7834550524599014297/6816750000000000000000000000000000 : ℝ)*base76 + (3224475609587264297/6816750000000000000000000000000000 : ℝ)*base78 + (69593819884124985703/6816750000000000000000000000000000 : ℝ)*base79 + (20314993004593/13633500000000000000000000000 : ℝ)*base81 + (10496249/10000000000000000000000 : ℝ)*base89 + (10496249/10000000000000000000000 : ℝ)*base91 + (10496249/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1159_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (111/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (359/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20361/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1159_s2_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142198863/10000000000 : ℝ)*x 0 + (2753806027/5000000000 : ℝ)*x 1 + (5161895819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142198863/10000000000 : ℝ)^261 ≤ (1623245261213/12500000000000 : ℝ)^197 := by
    have hnat : (2142198863 : ℕ)^261*12500000000000^197 ≤ 1623245261213^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142198863 10000000000 1623245261213 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753806027/5000000000 : ℝ)^261 ≤ (22687116691083/50000000000000 : ℝ)^197 := by
    have hnat : (2753806027 : ℕ)^261*50000000000000^197 ≤ 22687116691083^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753806027 5000000000 22687116691083 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161895819/10000000000 : ℝ)^261 ≤ (8327960903161/20000000000000 : ℝ)^197 := by
    have hnat : (5161895819 : ℕ)^261*20000000000000^197 ≤ 8327960903161^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161895819 10000000000 8327960903161 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142198863/10000000000 : ℝ), (2753806027/5000000000 : ℝ), (5161895819/10000000000 : ℝ)] ![(1623245261213/12500000000000 : ℝ), (22687116691083/50000000000000 : ℝ), (8327960903161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142198863/10000000000 : ℝ)|^261 ≤ (1623245261213/12500000000000 : ℝ)^197
        have hw : |(-2142198863/10000000000 : ℝ)|=(2142198863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753806027/5000000000 : ℝ)|^261 ≤ (22687116691083/50000000000000 : ℝ)^197
        have hw : |(2753806027/5000000000 : ℝ)|=(2753806027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5161895819/10000000000 : ℝ)|^261 ≤ (8327960903161/20000000000000 : ℝ)^197
        have hw : |(5161895819/10000000000 : ℝ)|=(5161895819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (537313903/1000000000 : ℝ)*x 0 + (-58045471/250000000 : ℝ)*x 1 + (5161898317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537313903/1000000000 : ℝ)^261 ≤ (21956162825189/50000000000000 : ℝ)^197 := by
    have hnat : (537313903 : ℕ)^261*50000000000000^197 ≤ 21956162825189^197*1000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537313903 1000000000 21956162825189 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58045471/250000000 : ℝ)^261 ≤ (14447843113037/100000000000000 : ℝ)^197 := by
    have hnat : (58045471 : ℕ)^261*100000000000000^197 ≤ 14447843113037^197*250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58045471 250000000 14447843113037 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161898317/10000000000 : ℝ)^261 ≤ (20819915606517/50000000000000 : ℝ)^197 := by
    have hnat : (5161898317 : ℕ)^261*50000000000000^197 ≤ 20819915606517^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161898317 10000000000 20819915606517 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537313903/1000000000 : ℝ), (-58045471/250000000 : ℝ), (5161898317/10000000000 : ℝ)] ![(21956162825189/50000000000000 : ℝ), (14447843113037/100000000000000 : ℝ), (20819915606517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537313903/1000000000 : ℝ)|^261 ≤ (21956162825189/50000000000000 : ℝ)^197
        have hw : |(537313903/1000000000 : ℝ)|=(537313903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58045471/250000000 : ℝ)|^261 ≤ (14447843113037/100000000000000 : ℝ)^197
        have hw : |(-58045471/250000000 : ℝ)|=(58045471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5161898317/10000000000 : ℝ)|^261 ≤ (20819915606517/50000000000000 : ℝ)^197
        have hw : |(5161898317/10000000000 : ℝ)|=(5161898317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1074627861/2000000000 : ℝ)*x 0 + (5161897757/10000000000 : ℝ)*x 1 + (-2321819207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074627861/2000000000 : ℝ)^261 ≤ (43912328627971/100000000000000 : ℝ)^197 := by
    have hnat : (1074627861 : ℕ)^261*100000000000000^197 ≤ 43912328627971^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074627861 2000000000 43912328627971 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161897757/10000000000 : ℝ)^261 ≤ (20819912614033/50000000000000 : ℝ)^197 := by
    have hnat : (5161897757 : ℕ)^261*50000000000000^197 ≤ 20819912614033^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161897757 10000000000 20819912614033 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2321819207/10000000000 : ℝ)^261 ≤ (7223923069331/50000000000000 : ℝ)^197 := by
    have hnat : (2321819207 : ℕ)^261*50000000000000^197 ≤ 7223923069331^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2321819207 10000000000 7223923069331 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074627861/2000000000 : ℝ), (5161897757/10000000000 : ℝ), (-2321819207/10000000000 : ℝ)] ![(43912328627971/100000000000000 : ℝ), (20819912614033/50000000000000 : ℝ), (7223923069331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074627861/2000000000 : ℝ)|^261 ≤ (43912328627971/100000000000000 : ℝ)^197
        have hw : |(1074627861/2000000000 : ℝ)|=(1074627861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161897757/10000000000 : ℝ)|^261 ≤ (20819912614033/50000000000000 : ℝ)^197
        have hw : |(5161897757/10000000000 : ℝ)|=(5161897757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2321819207/10000000000 : ℝ)|^261 ≤ (7223923069331/50000000000000 : ℝ)^197
        have hw : |(-2321819207/10000000000 : ℝ)|=(2321819207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4351933219/10000000000 : ℝ)*x 0 + (1005098547/2500000000 : ℝ)*x 1 + (2355238497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351933219/10000000000 : ℝ)^261 ≤ (166061823131/500000000000 : ℝ)^197 := by
    have hnat : (4351933219 : ℕ)^261*500000000000^197 ≤ 166061823131^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351933219 10000000000 166061823131 500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005098547/2500000000 : ℝ)^261 ≤ (1196096320521/4000000000000 : ℝ)^197 := by
    have hnat : (1005098547 : ℕ)^261*4000000000000^197 ≤ 1196096320521^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005098547 2500000000 1196096320521 4000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2355238497/5000000000 : ℝ)^261 ≤ (36885227340109/100000000000000 : ℝ)^197 := by
    have hnat : (2355238497 : ℕ)^261*100000000000000^197 ≤ 36885227340109^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355238497 5000000000 36885227340109 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351933219/10000000000 : ℝ), (1005098547/2500000000 : ℝ), (2355238497/5000000000 : ℝ)] ![(166061823131/500000000000 : ℝ), (1196096320521/4000000000000 : ℝ), (36885227340109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351933219/10000000000 : ℝ)|^261 ≤ (166061823131/500000000000 : ℝ)^197
        have hw : |(4351933219/10000000000 : ℝ)|=(4351933219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005098547/2500000000 : ℝ)|^261 ≤ (1196096320521/4000000000000 : ℝ)^197
        have hw : |(1005098547/2500000000 : ℝ)|=(1005098547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2355238497/5000000000 : ℝ)|^261 ≤ (36885227340109/100000000000000 : ℝ)^197
        have hw : |(2355238497/5000000000 : ℝ)|=(2355238497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071148153/5000000000 : ℝ)*x 0 + (5164252223/10000000000 : ℝ)*x 1 + (68815409/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071148153/5000000000 : ℝ)^261 ≤ (649337234723/5000000000000 : ℝ)^197 := by
    have hnat : (1071148153 : ℕ)^261*5000000000000^197 ≤ 649337234723^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071148153 5000000000 649337234723 5000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5164252223/10000000000 : ℝ)^261 ≤ (41664990311657/100000000000000 : ℝ)^197 := by
    have hnat : (5164252223 : ℕ)^261*100000000000000^197 ≤ 41664990311657^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164252223 10000000000 41664990311657 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68815409/125000000 : ℝ)^261 ≤ (45348264983469/100000000000000 : ℝ)^197 := by
    have hnat : (68815409 : ℕ)^261*100000000000000^197 ≤ 45348264983469^197*125000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68815409 125000000 45348264983469 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071148153/5000000000 : ℝ), (5164252223/10000000000 : ℝ), (68815409/125000000 : ℝ)] ![(649337234723/5000000000000 : ℝ), (41664990311657/100000000000000 : ℝ), (45348264983469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071148153/5000000000 : ℝ)|^261 ≤ (649337234723/5000000000000 : ℝ)^197
        have hw : |(-1071148153/5000000000 : ℝ)|=(1071148153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5164252223/10000000000 : ℝ)|^261 ≤ (41664990311657/100000000000000 : ℝ)^197
        have hw : |(5164252223/10000000000 : ℝ)|=(5164252223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68815409/125000000 : ℝ)|^261 ≤ (45348264983469/100000000000000 : ℝ)^197
        have hw : |(68815409/125000000 : ℝ)|=(68815409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2642661281/5000000000 : ℝ)*x 0 + (-1978483383/10000000000 : ℝ)*x 1 + (5505232711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642661281/5000000000 : ℝ)^261 ≤ (8592803349291/20000000000000 : ℝ)^197 := by
    have hnat : (2642661281 : ℕ)^261*20000000000000^197 ≤ 8592803349291^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642661281 5000000000 8592803349291 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978483383/10000000000 : ℝ)^261 ≤ (11687718344569/100000000000000 : ℝ)^197 := by
    have hnat : (1978483383 : ℕ)^261*100000000000000^197 ≤ 11687718344569^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978483383 10000000000 11687718344569 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505232711/10000000000 : ℝ)^261 ≤ (45348264885249/100000000000000 : ℝ)^197 := by
    have hnat : (5505232711 : ℕ)^261*100000000000000^197 ≤ 45348264885249^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505232711 10000000000 45348264885249 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642661281/5000000000 : ℝ), (-1978483383/10000000000 : ℝ), (5505232711/10000000000 : ℝ)] ![(8592803349291/20000000000000 : ℝ), (11687718344569/100000000000000 : ℝ), (45348264885249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642661281/5000000000 : ℝ)|^261 ≤ (8592803349291/20000000000000 : ℝ)^197
        have hw : |(2642661281/5000000000 : ℝ)|=(2642661281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978483383/10000000000 : ℝ)|^261 ≤ (11687718344569/100000000000000 : ℝ)^197
        have hw : |(-1978483383/10000000000 : ℝ)|=(1978483383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505232711/10000000000 : ℝ)|^261 ≤ (45348264885249/100000000000000 : ℝ)^197
        have hw : |(5505232711/10000000000 : ℝ)|=(5505232711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1321330669/2500000000 : ℝ)*x 0 + (1101046541/2000000000 : ℝ)*x 1 + (-494620809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321330669/2500000000 : ℝ)^261 ≤ (10741004493553/25000000000000 : ℝ)^197 := by
    have hnat : (1321330669 : ℕ)^261*25000000000000^197 ≤ 10741004493553^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321330669 2500000000 10741004493553 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101046541/2000000000 : ℝ)^261 ≤ (5668533102471/12500000000000 : ℝ)^197 := by
    have hnat : (1101046541 : ℕ)^261*12500000000000^197 ≤ 5668533102471^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101046541 2000000000 5668533102471 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494620809/2500000000 : ℝ)^261 ≤ (11687717194063/100000000000000 : ℝ)^197 := by
    have hnat : (494620809 : ℕ)^261*100000000000000^197 ≤ 11687717194063^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494620809 2500000000 11687717194063 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321330669/2500000000 : ℝ), (1101046541/2000000000 : ℝ), (-494620809/2500000000 : ℝ)] ![(10741004493553/25000000000000 : ℝ), (5668533102471/12500000000000 : ℝ), (11687717194063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321330669/2500000000 : ℝ)|^261 ≤ (10741004493553/25000000000000 : ℝ)^197
        have hw : |(1321330669/2500000000 : ℝ)|=(1321330669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101046541/2000000000 : ℝ)|^261 ≤ (5668533102471/12500000000000 : ℝ)^197
        have hw : |(1101046541/2000000000 : ℝ)|=(1101046541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494620809/2500000000 : ℝ)|^261 ≤ (11687717194063/100000000000000 : ℝ)^197
        have hw : |(-494620809/2500000000 : ℝ)|=(494620809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s2_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1088032327/2500000000 : ℝ)*x 0 + (4705775707/10000000000 : ℝ)*x 1 + (805028167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088032327/2500000000 : ℝ)^261 ≤ (16607173643149/50000000000000 : ℝ)^197 := by
    have hnat : (1088032327 : ℕ)^261*50000000000000^197 ≤ 16607173643149^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088032327 2500000000 16607173643149 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4705775707/10000000000 : ℝ)^261 ≤ (18418231171999/50000000000000 : ℝ)^197 := by
    have hnat : (4705775707 : ℕ)^261*50000000000000^197 ≤ 18418231171999^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705775707 10000000000 18418231171999 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805028167/2000000000 : ℝ)^261 ≤ (14974595179779/50000000000000 : ℝ)^197 := by
    have hnat : (805028167 : ℕ)^261*50000000000000^197 ≤ 14974595179779^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805028167 2000000000 14974595179779 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088032327/2500000000 : ℝ), (4705775707/10000000000 : ℝ), (805028167/2000000000 : ℝ)] ![(16607173643149/50000000000000 : ℝ), (18418231171999/50000000000000 : ℝ), (14974595179779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088032327/2500000000 : ℝ)|^261 ≤ (16607173643149/50000000000000 : ℝ)^197
        have hw : |(1088032327/2500000000 : ℝ)|=(1088032327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4705775707/10000000000 : ℝ)|^261 ≤ (18418231171999/50000000000000 : ℝ)^197
        have hw : |(4705775707/10000000000 : ℝ)|=(4705775707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805028167/2000000000 : ℝ)|^261 ≤ (14974595179779/50000000000000 : ℝ)^197
        have hw : |(805028167/2000000000 : ℝ)|=(805028167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (4573/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16453/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (359/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (359/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (359/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (359/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (359/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (359/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (359/6250 : ℝ) ^ (8351/2048 : ℝ) ≤ (872021524007059/100000000000000000000 : ℝ) := by
    have hpowers : (359/6250 : ℝ)^8351 ≤ (872021524007059/100000000000000000000 : ℝ)^2048 := by
      have hnat : (359 : ℕ)^8351*100000000000000000000^2048 ≤ 872021524007059^2048*6250^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        359 6250 872021524007059 100000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (359/6250 : ℝ)) (X := (872021524007059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20361/100000 : ℝ) ^ (8351/2048 : ℝ) ≤ (30378326236701653/20000000000000000000 : ℝ) := by
    have hpowers : (20361/100000 : ℝ)^8351 ≤ (30378326236701653/20000000000000000000 : ℝ)^2048 := by
      have hnat : (20361 : ℕ)^8351*20000000000000000000^2048 ≤ 30378326236701653^2048*100000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20361 100000 30378326236701653 20000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20361/100000 : ℝ)) (X := (30378326236701653/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000872021524007059/50000000000000000000 : ℝ) ≤ (10000042770646081/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50000872021524007059/50000000000000000000 : ℝ)^2048 ≤ (10000042770646081/10000000000000000 : ℝ)^8351 := by
      have hnat : (50000872021524007059 : ℕ)^2048*10000000000000000^8351 ≤ 10000042770646081^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000872021524007059 50000000000000000000 10000042770646081 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042770646081/10000000000000000 : ℝ)) (X := (50000872021524007059/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25038190913176878831/25000000000000000000 : ℝ) ≤ (10003744219352869/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (25038190913176878831/25000000000000000000 : ℝ)^2048 ≤ (10003744219352869/10000000000000000 : ℝ)^8351 := by
      have hnat : (25038190913176878831 : ℕ)^2048*10000000000000000^8351 ≤ 10003744219352869^8351*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038190913176878831 25000000000000000000 10003744219352869 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003744219352869/10000000000000000 : ℝ)) (X := (25038190913176878831/25000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10030378326236701653/10000000000000000000 : ℝ) ≤ (10007445668059657/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (10030378326236701653/10000000000000000000 : ℝ)^2048 ≤ (10007445668059657/10000000000000000 : ℝ)^8351 := by
      have hnat : (10030378326236701653 : ℕ)^2048*10000000000000000^8351 ≤ 10007445668059657^8351*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10030378326236701653 10000000000000000000 10007445668059657 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007445668059657/10000000000000000 : ℝ)) (X := (10030378326236701653/10000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(872021524007059/100000000000000000000 : ℝ) ≤ ((3109108573101918839/3110000000000000000 : ℝ)+2*(19688556951/7775000000000 : ℝ)*(359/6250 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (3109108573101918839/3110000000000000000 : ℝ)+2*(19688556951/7775000000000 : ℝ)*(359/6250 : ℝ)=(10000042770646081/10000000000000000 : ℝ) by norm_num, show 1+2*(872021524007059/100000000000000000000 : ℝ)=(50000872021524007059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30378326236701653/20000000000000000000 : ℝ)+(872021524007059/100000000000000000000 : ℝ) ≤ ((3109108573101918839/3110000000000000000 : ℝ)+(19688556951/7775000000000 : ℝ)*((20361/100000 : ℝ)+(359/6250 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (3109108573101918839/3110000000000000000 : ℝ)+(19688556951/7775000000000 : ℝ)*((20361/100000 : ℝ)+(359/6250 : ℝ))=(10003744219352869/10000000000000000 : ℝ) by norm_num, show 1+(30378326236701653/20000000000000000000 : ℝ)+(872021524007059/100000000000000000000 : ℝ)=(25038190913176878831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30378326236701653/20000000000000000000 : ℝ) ≤ ((3109108573101918839/3110000000000000000 : ℝ)+2*(19688556951/7775000000000 : ℝ)*(20361/100000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (3109108573101918839/3110000000000000000 : ℝ)+2*(19688556951/7775000000000 : ℝ)*(20361/100000 : ℝ)=(10007445668059657/10000000000000000 : ℝ) by norm_num, show 1+2*(30378326236701653/20000000000000000000 : ℝ)=(10030378326236701653/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3109108573101918839/3110000000000000000 : ℝ)*(X 1 0+X 2 0)+(19688556951/7775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (359/6250 : ℝ)) (hi := (20361/100000 : ℝ)) (c := (3109108573101918839/3110000000000000000 : ℝ)) (alpha := (19688556951/7775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3109108573101918839/3110000000000000000 : ℝ)*(X 0 1+X 2 1)+(19688556951/7775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (359/6250 : ℝ)) (hi := (20361/100000 : ℝ)) (c := (3109108573101918839/3110000000000000000 : ℝ)) (alpha := (19688556951/7775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3109108573101918839/3110000000000000000 : ℝ)*(X 0 2+X 1 2)+(19688556951/7775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (359/6250 : ℝ)) (hi := (20361/100000 : ℝ)) (c := (3109108573101918839/3110000000000000000 : ℝ)) (alpha := (19688556951/7775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2142198863/10000000000 : ℝ)*X 0 0+(2753806027/5000000000 : ℝ)*X 0 1+(5161895819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537313903/1000000000 : ℝ)*X 1 0+(-58045471/250000000 : ℝ)*X 1 1+(5161898317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074627861/2000000000 : ℝ)*X 2 0+(5161897757/10000000000 : ℝ)*X 2 1+(-2321819207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351933219/10000000000 : ℝ)*X 0 0+(1005098547/2500000000 : ℝ)*X 0 1+(2355238497/5000000000 : ℝ)*X 0 2+(4351933219/10000000000 : ℝ)*X 1 0+(1005098547/2500000000 : ℝ)*X 1 1+(2355238497/5000000000 : ℝ)*X 1 2+(4351933219/10000000000 : ℝ)*X 2 0+(1005098547/2500000000 : ℝ)*X 2 1+(2355238497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1071148153/5000000000 : ℝ)*X 0 0+(5164252223/10000000000 : ℝ)*X 0 1+(68815409/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642661281/5000000000 : ℝ)*X 1 0+(-1978483383/10000000000 : ℝ)*X 1 1+(5505232711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321330669/2500000000 : ℝ)*X 2 0+(1101046541/2000000000 : ℝ)*X 2 1+(-494620809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088032327/2500000000 : ℝ)*X 0 0+(4705775707/10000000000 : ℝ)*X 0 1+(805028167/2000000000 : ℝ)*X 0 2+(1088032327/2500000000 : ℝ)*X 1 0+(4705775707/10000000000 : ℝ)*X 1 1+(805028167/2000000000 : ℝ)*X 1 2+(1088032327/2500000000 : ℝ)*X 2 0+(4705775707/10000000000 : ℝ)*X 2 1+(805028167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1566787951733189081750684409/155500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301315287/25000000000000 : ℝ)*(base19) + (1024193437/100000000000000 : ℝ)*(base23) + (2583883/25000000000000 : ℝ)*(upper2) + (227138291/50000000000000 : ℝ)*(upper3) + (7486889/4000000000000 : ℝ)*(upper4) + (2170860107992123/100000000000000 : ℝ)*(major0) + (2170860107992123/100000000000000 : ℝ)*(major1) + (2170860107992123/100000000000000 : ℝ)*(major2) + (2892576053243503/100000000000000 : ℝ)*(sp0) + (2892599646153113/100000000000000 : ℝ)*(sp1) + (361574978402603/12500000000000 : ℝ)*(sp2) + (11321155856229/781250000000 : ℝ)*(sp3) + (24798170759/100000000000000 : ℝ)*(sp4) + (5539556221/50000000000000 : ℝ)*(sp7) + (724559514354877/50000000000000 : ℝ)*(f.failure) + (2892600851414261/100000000000000 : ℝ)*(f.sum) + (3022078679737/1555000000000000000000000000 : ℝ)*base65 + (49089721627505197/311000000000000000000000000000000 : ℝ)*base67 + (1659219614898494803/311000000000000000000000000000000 : ℝ)*base70 + (1559412616992505197/311000000000000000000000000000000 : ℝ)*base71 + (1174913565121/777500000000000000000000000 : ℝ)*base73 + (1015267683677505197/311000000000000000000000000000000 : ℝ)*base75 + (783221918237494803/311000000000000000000000000000000 : ℝ)*base78 + (817272364088505197/311000000000000000000000000000000 : ℝ)*base79 + (12378149121/777500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (23092361/5000000000000000000000 : ℝ)*base90 + (23092361/5000000000000000000000 : ℝ)*base92 + (23092361/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1593057287021772570750751743/155500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1118202541/50000000000000 : ℝ)*(base19) + (2404156407/100000000000000 : ℝ)*(base23) + (65260403/25000000000000 : ℝ)*(upper3) + (16212727/50000000000000 : ℝ)*(lower4) + (111540923/50000000000000 : ℝ)*(upper5) + (2200967813608593/100000000000000 : ℝ)*(major0) + (2200967813608593/100000000000000 : ℝ)*(major1) + (2200967813608593/100000000000000 : ℝ)*(major2) + (21597923051/100000000000000 : ℝ)*(sp1) + (12097304603/50000000000000 : ℝ)*(sp2) + (733179598495141/25000000000000 : ℝ)*(sp4) + (183293409978277/6250000000000 : ℝ)*(sp5) + (366586474401869/12500000000000 : ℝ)*(sp6) + (1469216891745237/100000000000000 : ℝ)*(sp7) + (1469216891745237/100000000000000 : ℝ)*(f.failure) + (733179598495141/25000000000000 : ℝ)*(f.sum) + (310651486507/97187500000000000000000000 : ℝ)*base65 + (869668526764816473/311000000000000000000000000000000 : ℝ)*base68 + (126115932048816473/311000000000000000000000000000000 : ℝ)*base70 + (508754886233816473/311000000000000000000000000000000 : ℝ)*base72 + (6122681634193/1555000000000000000000000000 : ℝ)*base74 + (1716151400377816473/311000000000000000000000000000000 : ℝ)*base76 + (1124765669381816473/311000000000000000000000000000000 : ℝ)*base78 + (1100605411394816473/311000000000000000000000000000000 : ℝ)*base80 + (3804408823683/1555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (43620159/10000000000000000000000 : ℝ)*base89 + (43620159/10000000000000000000000 : ℝ)*base91 + (43620159/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1159_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1159_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1159_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1159_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1159_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

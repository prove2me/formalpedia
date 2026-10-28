-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:27.341435+00:00
-- url     : https://prove2.me/submissions/a0f8d2f5-7984-461c-9147-9e156d3dd37f

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
theorem support_rectangle_w1181_s6_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074174781/5000000000 : ℝ)*x 0 + (1078520719/2000000000 : ℝ)*x 1 + (2633042557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074174781/5000000000 : ℝ)^4187 ≤ (1632256567077/12500000000000 : ℝ)^3163 := by
    have hnat : (1074174781 : ℕ)^4187*12500000000000^3163 ≤ 1632256567077^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074174781 5000000000 1632256567077 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078520719/2000000000 : ℝ)^4187 ≤ (44154000896869/100000000000000 : ℝ)^3163 := by
    have hnat : (1078520719 : ℕ)^4187*100000000000000^3163 ≤ 44154000896869^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078520719 2000000000 44154000896869 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633042557/5000000000 : ℝ)^4187 ≤ (42787946546419/100000000000000 : ℝ)^3163 := by
    have hnat : (2633042557 : ℕ)^4187*100000000000000^3163 ≤ 42787946546419^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633042557 5000000000 42787946546419 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074174781/5000000000 : ℝ), (1078520719/2000000000 : ℝ), (2633042557/5000000000 : ℝ)] ![(1632256567077/12500000000000 : ℝ), (44154000896869/100000000000000 : ℝ), (42787946546419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074174781/5000000000 : ℝ)|^4187 ≤ (1632256567077/12500000000000 : ℝ)^3163
        have hw : |(-1074174781/5000000000 : ℝ)|=(1074174781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078520719/2000000000 : ℝ)|^4187 ≤ (44154000896869/100000000000000 : ℝ)^3163
        have hw : |(1078520719/2000000000 : ℝ)|=(1078520719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633042557/5000000000 : ℝ)|^4187 ≤ (42787946546419/100000000000000 : ℝ)^3163
        have hw : |(2633042557/5000000000 : ℝ)|=(2633042557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672336129/5000000000 : ℝ)*x 0 + (-1106257953/5000000000 : ℝ)*x 1 + (5266085453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672336129/5000000000 : ℝ)^4187 ≤ (21817619351217/50000000000000 : ℝ)^3163 := by
    have hnat : (2672336129 : ℕ)^4187*50000000000000^3163 ≤ 21817619351217^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672336129 5000000000 21817619351217 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106257953/5000000000 : ℝ)^4187 ≤ (13576811094069/100000000000000 : ℝ)^3163 := by
    have hnat : (1106257953 : ℕ)^4187*100000000000000^3163 ≤ 13576811094069^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106257953 5000000000 13576811094069 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266085453/10000000000 : ℝ)^4187 ≤ (4278795019259/10000000000000 : ℝ)^3163 := by
    have hnat : (5266085453 : ℕ)^4187*10000000000000^3163 ≤ 4278795019259^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266085453 10000000000 4278795019259 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672336129/5000000000 : ℝ), (-1106257953/5000000000 : ℝ), (5266085453/10000000000 : ℝ)] ![(21817619351217/50000000000000 : ℝ), (13576811094069/100000000000000 : ℝ), (4278795019259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672336129/5000000000 : ℝ)|^4187 ≤ (21817619351217/50000000000000 : ℝ)^3163
        have hw : |(2672336129/5000000000 : ℝ)|=(2672336129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106257953/5000000000 : ℝ)|^4187 ≤ (13576811094069/100000000000000 : ℝ)^3163
        have hw : |(-1106257953/5000000000 : ℝ)|=(1106257953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266085453/10000000000 : ℝ)|^4187 ≤ (4278795019259/10000000000000 : ℝ)^3163
        have hw : |(5266085453/10000000000 : ℝ)|=(5266085453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344672253/10000000000 : ℝ)*x 0 + (5266084809/10000000000 : ℝ)*x 1 + (-442503353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344672253/10000000000 : ℝ)^4187 ≤ (43635238648397/100000000000000 : ℝ)^3163 := by
    have hnat : (5344672253 : ℕ)^4187*100000000000000^3163 ≤ 43635238648397^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344672253 10000000000 43635238648397 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266084809/10000000000 : ℝ)^4187 ≤ (2139397163297/5000000000000 : ℝ)^3163 := by
    have hnat : (5266084809 : ℕ)^4187*5000000000000^3163 ≤ 2139397163297^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266084809 10000000000 2139397163297 5000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442503353/2000000000 : ℝ)^4187 ≤ (2715363614341/20000000000000 : ℝ)^3163 := by
    have hnat : (442503353 : ℕ)^4187*20000000000000^3163 ≤ 2715363614341^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442503353 2000000000 2715363614341 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344672253/10000000000 : ℝ), (5266084809/10000000000 : ℝ), (-442503353/2000000000 : ℝ)] ![(43635238648397/100000000000000 : ℝ), (2139397163297/5000000000000 : ℝ), (2715363614341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344672253/10000000000 : ℝ)|^4187 ≤ (43635238648397/100000000000000 : ℝ)^3163
        have hw : |(5344672253/10000000000 : ℝ)|=(5344672253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266084809/10000000000 : ℝ)|^4187 ≤ (2139397163297/5000000000000 : ℝ)^3163
        have hw : |(5266084809/10000000000 : ℝ)|=(5266084809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442503353/2000000000 : ℝ)|^4187 ≤ (2715363614341/20000000000000 : ℝ)^3163
        have hw : |(-442503353/2000000000 : ℝ)|=(442503353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871838739/2000000000 : ℝ)*x 0 + (4234196427/10000000000 : ℝ)*x 1 + (897565919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871838739/2000000000 : ℝ)^4187 ≤ (6663406858043/20000000000000 : ℝ)^3163 := by
    have hnat : (871838739 : ℕ)^4187*20000000000000^3163 ≤ 6663406858043^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871838739 2000000000 6663406858043 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234196427/10000000000 : ℝ)^4187 ≤ (8014577432267/25000000000000 : ℝ)^3163 := by
    have hnat : (4234196427 : ℕ)^4187*25000000000000^3163 ≤ 8014577432267^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234196427 10000000000 8014577432267 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897565919/2000000000 : ℝ)^4187 ≤ (34624655964899/100000000000000 : ℝ)^3163 := by
    have hnat : (897565919 : ℕ)^4187*100000000000000^3163 ≤ 34624655964899^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897565919 2000000000 34624655964899 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871838739/2000000000 : ℝ), (4234196427/10000000000 : ℝ), (897565919/2000000000 : ℝ)] ![(6663406858043/20000000000000 : ℝ), (8014577432267/25000000000000 : ℝ), (34624655964899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871838739/2000000000 : ℝ)|^4187 ≤ (6663406858043/20000000000000 : ℝ)^3163
        have hw : |(871838739/2000000000 : ℝ)|=(871838739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234196427/10000000000 : ℝ)|^4187 ≤ (8014577432267/25000000000000 : ℝ)^3163
        have hw : |(4234196427/10000000000 : ℝ)|=(4234196427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897565919/2000000000 : ℝ)|^4187 ≤ (34624655964899/100000000000000 : ℝ)^3163
        have hw : |(897565919/2000000000 : ℝ)|=(897565919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-429670867/2000000000 : ℝ)*x 0 + (2633202329/5000000000 : ℝ)*x 1 + (1348070737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429670867/2000000000 : ℝ)^4187 ≤ (13058090939941/100000000000000 : ℝ)^3163 := by
    have hnat : (429670867 : ℕ)^4187*100000000000000^3163 ≤ 13058090939941^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429670867 2000000000 13058090939941 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633202329/5000000000 : ℝ)^4187 ≤ (21395691744483/50000000000000 : ℝ)^3163 := by
    have hnat : (2633202329 : ℕ)^4187*50000000000000^3163 ≤ 21395691744483^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633202329 5000000000 21395691744483 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348070737/2500000000 : ℝ)^4187 ≤ (22075262774289/50000000000000 : ℝ)^3163 := by
    have hnat : (1348070737 : ℕ)^4187*50000000000000^3163 ≤ 22075262774289^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348070737 2500000000 22075262774289 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429670867/2000000000 : ℝ), (2633202329/5000000000 : ℝ), (1348070737/2500000000 : ℝ)] ![(13058090939941/100000000000000 : ℝ), (21395691744483/50000000000000 : ℝ), (22075262774289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429670867/2000000000 : ℝ)|^4187 ≤ (13058090939941/100000000000000 : ℝ)^3163
        have hw : |(-429670867/2000000000 : ℝ)|=(429670867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633202329/5000000000 : ℝ)|^4187 ≤ (21395691744483/50000000000000 : ℝ)^3163
        have hw : |(2633202329/5000000000 : ℝ)|=(2633202329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348070737/2500000000 : ℝ)|^4187 ≤ (22075262774289/50000000000000 : ℝ)^3163
        have hw : |(1348070737/2500000000 : ℝ)|=(1348070737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21250109/40000000 : ℝ)*x 0 + (-417263649/2000000000 : ℝ)*x 1 + (5392282967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21250109/40000000 : ℝ)^4187 ≤ (5411021795539/12500000000000 : ℝ)^3163 := by
    have hnat : (21250109 : ℕ)^4187*12500000000000^3163 ≤ 5411021795539^3163*40000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21250109 40000000 5411021795539 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417263649/2000000000 : ℝ)^4187 ≤ (12561299875381/100000000000000 : ℝ)^3163 := by
    have hnat : (417263649 : ℕ)^4187*100000000000000^3163 ≤ 12561299875381^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417263649 2000000000 12561299875381 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392282967/10000000000 : ℝ)^4187 ≤ (11037631438627/25000000000000 : ℝ)^3163 := by
    have hnat : (5392282967 : ℕ)^4187*25000000000000^3163 ≤ 11037631438627^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392282967 10000000000 11037631438627 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21250109/40000000 : ℝ), (-417263649/2000000000 : ℝ), (5392282967/10000000000 : ℝ)] ![(5411021795539/12500000000000 : ℝ), (12561299875381/100000000000000 : ℝ), (11037631438627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21250109/40000000 : ℝ)|^4187 ≤ (5411021795539/12500000000000 : ℝ)^3163
        have hw : |(21250109/40000000 : ℝ)|=(21250109/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417263649/2000000000 : ℝ)|^4187 ≤ (12561299875381/100000000000000 : ℝ)^3163
        have hw : |(-417263649/2000000000 : ℝ)|=(417263649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392282967/10000000000 : ℝ)|^4187 ≤ (11037631438627/25000000000000 : ℝ)^3163
        have hw : |(5392282967/10000000000 : ℝ)|=(5392282967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328131817/2500000000 : ℝ)*x 0 + (2696141479/5000000000 : ℝ)*x 1 + (-260789779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328131817/2500000000 : ℝ)^4187 ≤ (8657634911693/20000000000000 : ℝ)^3163 := by
    have hnat : (1328131817 : ℕ)^4187*20000000000000^3163 ≤ 8657634911693^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328131817 2500000000 8657634911693 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696141479/5000000000 : ℝ)^4187 ≤ (22075262828481/50000000000000 : ℝ)^3163 := by
    have hnat : (2696141479 : ℕ)^4187*50000000000000^3163 ≤ 22075262828481^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696141479 5000000000 22075262828481 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260789779/1250000000 : ℝ)^4187 ≤ (12561299771771/100000000000000 : ℝ)^3163 := by
    have hnat : (260789779 : ℕ)^4187*100000000000000^3163 ≤ 12561299771771^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260789779 1250000000 12561299771771 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328131817/2500000000 : ℝ), (2696141479/5000000000 : ℝ), (-260789779/1250000000 : ℝ)] ![(8657634911693/20000000000000 : ℝ), (22075262828481/50000000000000 : ℝ), (12561299771771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328131817/2500000000 : ℝ)|^4187 ≤ (8657634911693/20000000000000 : ℝ)^3163
        have hw : |(1328131817/2500000000 : ℝ)|=(1328131817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696141479/5000000000 : ℝ)|^4187 ≤ (22075262828481/50000000000000 : ℝ)^3163
        have hw : |(2696141479/5000000000 : ℝ)|=(2696141479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260789779/1250000000 : ℝ)|^4187 ≤ (12561299771771/100000000000000 : ℝ)^3163
        have hw : |(-260789779/1250000000 : ℝ)|=(260789779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s6_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871840733/2000000000 : ℝ)*x 0 + (4487188447/10000000000 : ℝ)*x 1 + (423483967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871840733/2000000000 : ℝ)^4187 ≤ (33317135159573/100000000000000 : ℝ)^3163 := by
    have hnat : (871840733 : ℕ)^4187*100000000000000^3163 ≤ 33317135159573^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871840733 2000000000 33317135159573 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487188447/10000000000 : ℝ)^4187 ≤ (540907938729/1562500000000 : ℝ)^3163 := by
    have hnat : (4487188447 : ℕ)^4187*1562500000000^3163 ≤ 540907938729^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487188447 10000000000 540907938729 1562500000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423483967/1000000000 : ℝ)^4187 ≤ (8016189187707/25000000000000 : ℝ)^3163 := by
    have hnat : (423483967 : ℕ)^4187*25000000000000^3163 ≤ 8016189187707^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423483967 1000000000 8016189187707 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871840733/2000000000 : ℝ), (4487188447/10000000000 : ℝ), (423483967/1000000000 : ℝ)] ![(33317135159573/100000000000000 : ℝ), (540907938729/1562500000000 : ℝ), (8016189187707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871840733/2000000000 : ℝ)|^4187 ≤ (33317135159573/100000000000000 : ℝ)^3163
        have hw : |(871840733/2000000000 : ℝ)|=(871840733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487188447/10000000000 : ℝ)|^4187 ≤ (540907938729/1562500000000 : ℝ)^3163
        have hw : |(4487188447/10000000000 : ℝ)|=(4487188447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423483967/1000000000 : ℝ)|^4187 ≤ (8016189187707/25000000000000 : ℝ)^3163
        have hw : |(423483967/1000000000 : ℝ)|=(423483967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11371/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (1724476058911081/12500000000000000000 : ℝ) := by
    have hpowers : (11371/100000 : ℝ)^8373 ≤ (1724476058911081/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11371 : ℕ)^8373*12500000000000000000^2048 ≤ 1724476058911081^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11371 100000 1724476058911081 12500000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11371/100000 : ℝ)) (X := (1724476058911081/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (8373/2048 : ℝ) ≤ (33290083622434549/100000000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^8373 ≤ (33290083622434549/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8373*100000000000000000000^2048 ≤ 33290083622434549^2048*20000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 33290083622434549 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (33290083622434549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251724476058911081/6250000000000000000 : ℝ) ≤ (10000674808832623/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (6251724476058911081/6250000000000000000 : ℝ)^2048 ≤ (10000674808832623/10000000000000000 : ℝ)^8373 := by
      have hnat : (6251724476058911081 : ℕ)^2048*10000000000000000^8373 ≤ 10000674808832623^8373*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251724476058911081 6250000000000000000 10000674808832623 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674808832623/10000000000000000 : ℝ)) (X := (6251724476058911081/6250000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047085892093723197/100000000000000000000 : ℝ) ≤ (10001151496021197/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (100047085892093723197/100000000000000000000 : ℝ)^2048 ≤ (10001151496021197/10000000000000000 : ℝ)^8373 := by
      have hnat : (100047085892093723197 : ℕ)^2048*10000000000000000^8373 ≤ 10001151496021197^8373*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047085892093723197 100000000000000000000 10001151496021197 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001151496021197/10000000000000000 : ℝ)) (X := (100047085892093723197/100000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033290083622434549/50000000000000000000 : ℝ) ≤ (10001628183209771/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50033290083622434549/50000000000000000000 : ℝ)^2048 ≤ (10001628183209771/10000000000000000 : ℝ)^8373 := by
      have hnat : (50033290083622434549 : ℕ)^2048*10000000000000000^8373 ≤ 10001628183209771^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033290083622434549 50000000000000000000 10001628183209771 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001628183209771/10000000000000000 : ℝ)) (X := (50033290083622434549/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1724476058911081/12500000000000000000 : ℝ) ≤ ((13665502053652920687/13670000000000000000 : ℝ)+2*(238343594287/136700000000000 : ℝ)*(11371/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (13665502053652920687/13670000000000000000 : ℝ)+2*(238343594287/136700000000000 : ℝ)*(11371/100000 : ℝ)=(10000674808832623/10000000000000000 : ℝ) by norm_num, show 1+2*(1724476058911081/12500000000000000000 : ℝ)=(6251724476058911081/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33290083622434549/100000000000000000000 : ℝ)+(1724476058911081/12500000000000000000 : ℝ) ≤ ((13665502053652920687/13670000000000000000 : ℝ)+(238343594287/136700000000000 : ℝ)*((2821/20000 : ℝ)+(11371/100000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (13665502053652920687/13670000000000000000 : ℝ)+(238343594287/136700000000000 : ℝ)*((2821/20000 : ℝ)+(11371/100000 : ℝ))=(10001151496021197/10000000000000000 : ℝ) by norm_num, show 1+(33290083622434549/100000000000000000000 : ℝ)+(1724476058911081/12500000000000000000 : ℝ)=(100047085892093723197/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33290083622434549/100000000000000000000 : ℝ) ≤ ((13665502053652920687/13670000000000000000 : ℝ)+2*(238343594287/136700000000000 : ℝ)*(2821/20000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (13665502053652920687/13670000000000000000 : ℝ)+2*(238343594287/136700000000000 : ℝ)*(2821/20000 : ℝ)=(10001628183209771/10000000000000000 : ℝ) by norm_num, show 1+2*(33290083622434549/100000000000000000000 : ℝ)=(50033290083622434549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13665502053652920687/13670000000000000000 : ℝ)*(X 1 0+X 2 0)+(238343594287/136700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (13665502053652920687/13670000000000000000 : ℝ)) (alpha := (238343594287/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13665502053652920687/13670000000000000000 : ℝ)*(X 0 1+X 2 1)+(238343594287/136700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (13665502053652920687/13670000000000000000 : ℝ)) (alpha := (238343594287/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13665502053652920687/13670000000000000000 : ℝ)*(X 0 2+X 1 2)+(238343594287/136700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (13665502053652920687/13670000000000000000 : ℝ)) (alpha := (238343594287/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1074174781/5000000000 : ℝ)*X 0 0+(1078520719/2000000000 : ℝ)*X 0 1+(2633042557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672336129/5000000000 : ℝ)*X 1 0+(-1106257953/5000000000 : ℝ)*X 1 1+(5266085453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344672253/10000000000 : ℝ)*X 2 0+(5266084809/10000000000 : ℝ)*X 2 1+(-442503353/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871838739/2000000000 : ℝ)*X 0 0+(4234196427/10000000000 : ℝ)*X 0 1+(897565919/2000000000 : ℝ)*X 0 2+(871838739/2000000000 : ℝ)*X 1 0+(4234196427/10000000000 : ℝ)*X 1 1+(897565919/2000000000 : ℝ)*X 1 2+(871838739/2000000000 : ℝ)*X 2 0+(4234196427/10000000000 : ℝ)*X 2 1+(897565919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-429670867/2000000000 : ℝ)*X 0 0+(2633202329/5000000000 : ℝ)*X 0 1+(1348070737/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21250109/40000000 : ℝ)*X 1 0+(-417263649/2000000000 : ℝ)*X 1 1+(5392282967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328131817/2500000000 : ℝ)*X 2 0+(2696141479/5000000000 : ℝ)*X 2 1+(-260789779/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871840733/2000000000 : ℝ)*X 0 0+(4487188447/10000000000 : ℝ)*X 0 1+(423483967/1000000000 : ℝ)*X 0 2+(871840733/2000000000 : ℝ)*X 1 0+(4487188447/10000000000 : ℝ)*X 1 1+(423483967/1000000000 : ℝ)*X 1 2+(871840733/2000000000 : ℝ)*X 2 0+(4487188447/10000000000 : ℝ)*X 2 1+(423483967/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8334997789976015688560766573/683500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (753893751/50000000000000 : ℝ)*(base19) + (1440770157/100000000000000 : ℝ)*(base23) + (75496479/100000000000000 : ℝ)*(upper2) + (468236343/100000000000000 : ℝ)*(upper3) + (5923432621359007/100000000000000 : ℝ)*(major0) + (5923432621359007/100000000000000 : ℝ)*(major1) + (5923432621359007/100000000000000 : ℝ)*(major2) + (7904051675289283/100000000000000 : ℝ)*(sp0) + (3952045428240683/50000000000000 : ℝ)*(sp1) + (7904057523884887/100000000000000 : ℝ)*(sp2) + (492841659556273/12500000000000 : ℝ)*(sp3) + (20344489793/50000000000000 : ℝ)*(sp4) + (260934483/781250000000 : ℝ)*(sp6) + (7839102567/20000000000000 : ℝ)*(sp7) + (3942772471963019/100000000000000 : ℝ)*(f.failure) + (1976023091067217/25000000000000 : ℝ)*(f.sum) + (7364696857961/1708750000000000000000000000 : ℝ)*base65 + (8805571281437022191/1367000000000000000000000000000000 : ℝ)*base68 + (1154334124215022191/1367000000000000000000000000000000 : ℝ)*base70 + (22895868469063977809/1367000000000000000000000000000000 : ℝ)*base71 + (5864192730093/3417500000000000000000000000 : ℝ)*base74 + (33977243252848977809/1367000000000000000000000000000000 : ℝ)*base75 + (30235908238958977809/1367000000000000000000000000000000 : ℝ)*base77 + (26895398512828977809/1367000000000000000000000000000000 : ℝ)*base79 + (10521659842959/1708750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (12411953/10000000000000000000000 : ℝ)*base90 + (12411953/10000000000000000000000 : ℝ)*base92 + (12411953/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13286613839812742815377/6835000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372239499/100000000000000 : ℝ)*(base19) + (428663591/100000000000000 : ℝ)*(base23) + (23782141/50000000000000 : ℝ)*(upper3) + (2343713/25000000000000 : ℝ)*(lower4) + (36394101/100000000000000 : ℝ)*(upper5) + (2976737743738927/50000000000000 : ℝ)*(major0) + (2976737743738927/50000000000000 : ℝ)*(major1) + (2976737743738927/50000000000000 : ℝ)*(major2) + (11018211537/100000000000000 : ℝ)*(sp1) + (12978423883/100000000000000 : ℝ)*(sp2) + (7944181218157281/100000000000000 : ℝ)*(sp4) + (1986042456926561/25000000000000 : ℝ)*(sp5) + (496510488191863/6250000000000 : ℝ)*(sp6) + (61918276437523/1562500000000 : ℝ)*(sp7) + (61918276437523/1562500000000 : ℝ)*(f.failure) + (7944181218157281/100000000000000 : ℝ)*(f.sum) + (38849109556977/6835000000000000000000000000 : ℝ)*base66 + (8130625681323382849/683500000000000000000000000000000 : ℝ)*base67 + (30036749932382849/683500000000000000000000000000000 : ℝ)*base69 + (2950943103000617151/683500000000000000000000000000000 : ℝ)*base72 + (3292389045343/1708750000000000000000000000 : ℝ)*base74 + (4845381176778882849/683500000000000000000000000000000 : ℝ)*base75 + (4023732849850117151/683500000000000000000000000000000 : ℝ)*base78 + (9381198304312117151/683500000000000000000000000000000 : ℝ)*base80 + (14757952815217/6835000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2222399/156250000000000000000 : ℝ)*base89 + (2222399/156250000000000000000 : ℝ)*base91 + (2222399/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1181_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1181_s7_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148374847/10000000000 : ℝ)*x 0 + (1078467157/2000000000 : ℝ)*x 1 + (5266336071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148374847/10000000000 : ℝ)^4187 ≤ (3264563994701/25000000000000 : ℝ)^3163 := by
    have hnat : (2148374847 : ℕ)^4187*25000000000000^3163 ≤ 3264563994701^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148374847 10000000000 3264563994701 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078467157/2000000000 : ℝ)^4187 ≤ (44151098220399/100000000000000 : ℝ)^3163 := by
    have hnat : (1078467157 : ℕ)^4187*100000000000000^3163 ≤ 44151098220399^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078467157 2000000000 44151098220399 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266336071/10000000000 : ℝ)^4187 ≤ (42790645777111/100000000000000 : ℝ)^3163 := by
    have hnat : (5266336071 : ℕ)^4187*100000000000000^3163 ≤ 42790645777111^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266336071 10000000000 42790645777111 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148374847/10000000000 : ℝ), (1078467157/2000000000 : ℝ), (5266336071/10000000000 : ℝ)] ![(3264563994701/25000000000000 : ℝ), (44151098220399/100000000000000 : ℝ), (42790645777111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148374847/10000000000 : ℝ)|^4187 ≤ (3264563994701/25000000000000 : ℝ)^3163
        have hw : |(-2148374847/10000000000 : ℝ)|=(2148374847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078467157/2000000000 : ℝ)|^4187 ≤ (44151098220399/100000000000000 : ℝ)^3163
        have hw : |(1078467157/2000000000 : ℝ)|=(1078467157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266336071/10000000000 : ℝ)|^4187 ≤ (42790645777111/100000000000000 : ℝ)^3163
        have hw : |(5266336071/10000000000 : ℝ)|=(5266336071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334037761/625000000 : ℝ)*x 0 + (-553068653/2500000000 : ℝ)*x 1 + (658292011/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334037761/625000000 : ℝ)^4187 ≤ (43634502916543/100000000000000 : ℝ)^3163 := by
    have hnat : (334037761 : ℕ)^4187*100000000000000^3163 ≤ 43634502916543^3163*625000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334037761 625000000 43634502916543 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553068653/2500000000 : ℝ)^4187 ≤ (13574851103423/100000000000000 : ℝ)^3163 := by
    have hnat : (553068653 : ℕ)^4187*100000000000000^3163 ≤ 13574851103423^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553068653 2500000000 13574851103423 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658292011/1250000000 : ℝ)^4187 ≤ (1069766148999/2500000000000 : ℝ)^3163 := by
    have hnat : (658292011 : ℕ)^4187*2500000000000^3163 ≤ 1069766148999^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658292011 1250000000 1069766148999 2500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334037761/625000000 : ℝ), (-553068653/2500000000 : ℝ), (658292011/1250000000 : ℝ)] ![(43634502916543/100000000000000 : ℝ), (13574851103423/100000000000000 : ℝ), (1069766148999/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334037761/625000000 : ℝ)|^4187 ≤ (43634502916543/100000000000000 : ℝ)^3163
        have hw : |(334037761/625000000 : ℝ)|=(334037761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553068653/2500000000 : ℝ)|^4187 ≤ (13574851103423/100000000000000 : ℝ)^3163
        have hw : |(-553068653/2500000000 : ℝ)|=(553068653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658292011/1250000000 : ℝ)|^4187 ≤ (1069766148999/2500000000000 : ℝ)^3163
        have hw : |(658292011/1250000000 : ℝ)|=(658292011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068920837/2000000000 : ℝ)*x 0 + (5266336081/10000000000 : ℝ)*x 1 + (-2212274609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068920837/2000000000 : ℝ)^4187 ≤ (2727156438363/6250000000000 : ℝ)^3163 := by
    have hnat : (1068920837 : ℕ)^4187*6250000000000^3163 ≤ 2727156438363^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068920837 2000000000 2727156438363 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266336081/10000000000 : ℝ)^4187 ≤ (42790645884669/100000000000000 : ℝ)^3163 := by
    have hnat : (5266336081 : ℕ)^4187*100000000000000^3163 ≤ 42790645884669^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266336081 10000000000 42790645884669 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212274609/10000000000 : ℝ)^4187 ≤ (2714970215811/20000000000000 : ℝ)^3163 := by
    have hnat : (2212274609 : ℕ)^4187*20000000000000^3163 ≤ 2714970215811^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212274609 10000000000 2714970215811 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068920837/2000000000 : ℝ), (5266336081/10000000000 : ℝ), (-2212274609/10000000000 : ℝ)] ![(2727156438363/6250000000000 : ℝ), (42790645884669/100000000000000 : ℝ), (2714970215811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068920837/2000000000 : ℝ)|^4187 ≤ (2727156438363/6250000000000 : ℝ)^3163
        have hw : |(1068920837/2000000000 : ℝ)|=(1068920837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266336081/10000000000 : ℝ)|^4187 ≤ (42790645884669/100000000000000 : ℝ)^3163
        have hw : |(5266336081/10000000000 : ℝ)|=(5266336081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2212274609/10000000000 : ℝ)|^4187 ≤ (2714970215811/20000000000000 : ℝ)^3163
        have hw : |(-2212274609/10000000000 : ℝ)|=(2212274609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359207133/10000000000 : ℝ)*x 0 + (52933939/125000000 : ℝ)*x 1 + (280456703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359207133/10000000000 : ℝ)^4187 ≤ (4164646280793/12500000000000 : ℝ)^3163 := by
    have hnat : (4359207133 : ℕ)^4187*12500000000000^3163 ≤ 4164646280793^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359207133 10000000000 4164646280793 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52933939/125000000 : ℝ)^4187 ≤ (320635084007/1000000000000 : ℝ)^3163 := by
    have hnat : (52933939 : ℕ)^4187*1000000000000^3163 ≤ 320635084007^3163*125000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52933939 125000000 320635084007 1000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280456703/625000000 : ℝ)^4187 ≤ (865483033527/2500000000000 : ℝ)^3163 := by
    have hnat : (280456703 : ℕ)^4187*2500000000000^3163 ≤ 865483033527^3163*625000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280456703 625000000 865483033527 2500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359207133/10000000000 : ℝ), (52933939/125000000 : ℝ), (280456703/625000000 : ℝ)] ![(4164646280793/12500000000000 : ℝ), (320635084007/1000000000000 : ℝ), (865483033527/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359207133/10000000000 : ℝ)|^4187 ≤ (4164646280793/12500000000000 : ℝ)^3163
        have hw : |(4359207133/10000000000 : ℝ)|=(4359207133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52933939/125000000 : ℝ)|^4187 ≤ (320635084007/1000000000000 : ℝ)^3163
        have hw : |(52933939/125000000 : ℝ)|=(52933939/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280456703/625000000 : ℝ)|^4187 ≤ (865483033527/2500000000000 : ℝ)^3163
        have hw : |(280456703/625000000 : ℝ)|=(280456703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-537094911/2500000000 : ℝ)*x 0 + (164582911/312500000 : ℝ)*x 1 + (1078403511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537094911/2500000000 : ℝ)^4187 ≤ (13058294575379/100000000000000 : ℝ)^3163 := by
    have hnat : (537094911 : ℕ)^4187*100000000000000^3163 ≤ 13058294575379^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537094911 2500000000 13058294575379 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164582911/312500000 : ℝ)^4187 ≤ (42794056280547/100000000000000 : ℝ)^3163 := by
    have hnat : (164582911 : ℕ)^4187*100000000000000^3163 ≤ 42794056280547^3163*312500000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164582911 312500000 42794056280547 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078403511/2000000000 : ℝ)^4187 ≤ (44147649124089/100000000000000 : ℝ)^3163 := by
    have hnat : (1078403511 : ℕ)^4187*100000000000000^3163 ≤ 44147649124089^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078403511 2000000000 44147649124089 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537094911/2500000000 : ℝ), (164582911/312500000 : ℝ), (1078403511/2000000000 : ℝ)] ![(13058294575379/100000000000000 : ℝ), (42794056280547/100000000000000 : ℝ), (44147649124089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537094911/2500000000 : ℝ)|^4187 ≤ (13058294575379/100000000000000 : ℝ)^3163
        have hw : |(-537094911/2500000000 : ℝ)|=(537094911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164582911/312500000 : ℝ)|^4187 ≤ (42794056280547/100000000000000 : ℝ)^3163
        have hw : |(164582911/312500000 : ℝ)|=(164582911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078403511/2000000000 : ℝ)|^4187 ≤ (44147649124089/100000000000000 : ℝ)^3163
        have hw : |(1078403511/2000000000 : ℝ)|=(1078403511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312590817/10000000000 : ℝ)*x 0 + (-1043296569/5000000000 : ℝ)*x 1 + (5392017557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312590817/10000000000 : ℝ)^4187 ≤ (43288860017383/100000000000000 : ℝ)^3163 := by
    have hnat : (5312590817 : ℕ)^4187*100000000000000^3163 ≤ 43288860017383^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312590817 10000000000 43288860017383 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043296569/5000000000 : ℝ)^4187 ≤ (1256349081667/10000000000000 : ℝ)^3163 := by
    have hnat : (1043296569 : ℕ)^4187*10000000000000^3163 ≤ 1256349081667^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043296569 5000000000 1256349081667 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392017557/10000000000 : ℝ)^4187 ≤ (22073824572883/50000000000000 : ℝ)^3163 := by
    have hnat : (5392017557 : ℕ)^4187*50000000000000^3163 ≤ 22073824572883^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392017557 10000000000 22073824572883 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312590817/10000000000 : ℝ), (-1043296569/5000000000 : ℝ), (5392017557/10000000000 : ℝ)] ![(43288860017383/100000000000000 : ℝ), (1256349081667/10000000000000 : ℝ), (22073824572883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312590817/10000000000 : ℝ)|^4187 ≤ (43288860017383/100000000000000 : ℝ)^3163
        have hw : |(5312590817/10000000000 : ℝ)|=(5312590817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043296569/5000000000 : ℝ)|^4187 ≤ (1256349081667/10000000000000 : ℝ)^3163
        have hw : |(-1043296569/5000000000 : ℝ)|=(1043296569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392017557/10000000000 : ℝ)|^4187 ≤ (22073824572883/50000000000000 : ℝ)^3163
        have hw : |(5392017557/10000000000 : ℝ)|=(5392017557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062518163/2000000000 : ℝ)*x 0 + (5392017559/10000000000 : ℝ)*x 1 + (-2086593139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062518163/2000000000 : ℝ)^4187 ≤ (4328885999581/10000000000000 : ℝ)^3163 := by
    have hnat : (1062518163 : ℕ)^4187*10000000000000^3163 ≤ 4328885999581^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062518163 2000000000 4328885999581 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392017559/10000000000 : ℝ)^4187 ≤ (22073824583721/50000000000000 : ℝ)^3163 := by
    have hnat : (5392017559 : ℕ)^4187*50000000000000^3163 ≤ 22073824583721^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392017559 10000000000 22073824583721 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086593139/10000000000 : ℝ)^4187 ≤ (39260908827/312500000000 : ℝ)^3163 := by
    have hnat : (2086593139 : ℕ)^4187*312500000000^3163 ≤ 39260908827^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086593139 10000000000 39260908827 312500000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062518163/2000000000 : ℝ), (5392017559/10000000000 : ℝ), (-2086593139/10000000000 : ℝ)] ![(4328885999581/10000000000000 : ℝ), (22073824583721/50000000000000 : ℝ), (39260908827/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062518163/2000000000 : ℝ)|^4187 ≤ (4328885999581/10000000000000 : ℝ)^3163
        have hw : |(1062518163/2000000000 : ℝ)|=(1062518163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392017559/10000000000 : ℝ)|^4187 ≤ (22073824583721/50000000000000 : ℝ)^3163
        have hw : |(5392017559/10000000000 : ℝ)|=(5392017559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086593139/10000000000 : ℝ)|^4187 ≤ (39260908827/312500000000 : ℝ)^3163
        have hw : |(-2086593139/10000000000 : ℝ)|=(2086593139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s7_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089804183/2500000000 : ℝ)*x 0 + (4486671619/10000000000 : ℝ)*x 1 + (529419133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089804183/2500000000 : ℝ)^4187 ≤ (8329316840571/25000000000000 : ℝ)^3163 := by
    have hnat : (1089804183 : ℕ)^4187*25000000000000^3163 ≤ 8329316840571^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089804183 2500000000 8329316840571 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486671619/10000000000 : ℝ)^4187 ≤ (34612830062363/100000000000000 : ℝ)^3163 := by
    have hnat : (4486671619 : ℕ)^4187*100000000000000^3163 ≤ 34612830062363^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486671619 10000000000 34612830062363 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529419133/1250000000 : ℝ)^4187 ≤ (6413980512901/20000000000000 : ℝ)^3163 := by
    have hnat : (529419133 : ℕ)^4187*20000000000000^3163 ≤ 6413980512901^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529419133 1250000000 6413980512901 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089804183/2500000000 : ℝ), (4486671619/10000000000 : ℝ), (529419133/1250000000 : ℝ)] ![(8329316840571/25000000000000 : ℝ), (34612830062363/100000000000000 : ℝ), (6413980512901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089804183/2500000000 : ℝ)|^4187 ≤ (8329316840571/25000000000000 : ℝ)^3163
        have hw : |(1089804183/2500000000 : ℝ)|=(1089804183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486671619/10000000000 : ℝ)|^4187 ≤ (34612830062363/100000000000000 : ℝ)^3163
        have hw : |(4486671619/10000000000 : ℝ)|=(4486671619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529419133/1250000000 : ℝ)|^4187 ≤ (6413980512901/20000000000000 : ℝ)^3163
        have hw : |(529419133/1250000000 : ℝ)|=(529419133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1759/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11397/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (13925229882539979/100000000000000000000 : ℝ) := by
    have hpowers : (11397/100000 : ℝ)^8373 ≤ (13925229882539979/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11397 : ℕ)^8373*100000000000000000000^2048 ≤ 13925229882539979^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11397 100000 13925229882539979 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11397/100000 : ℝ)) (X := (13925229882539979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (4127591508653297/12500000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^8373 ≤ (4127591508653297/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14077 : ℕ)^8373*12500000000000000000^2048 ≤ 4127591508653297^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 4127591508653297 12500000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (4127591508653297/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013925229882539979/50000000000000000000 : ℝ) ≤ (2500170284672981/2500000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50013925229882539979/50000000000000000000 : ℝ)^2048 ≤ (2500170284672981/2500000000000000 : ℝ)^8373 := by
      have hnat : (50013925229882539979 : ℕ)^2048*2500000000000000^8373 ≤ 2500170284672981^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013925229882539979 50000000000000000000 2500170284672981 2500000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500170284672981/2500000000000000 : ℝ)) (X := (50013925229882539979/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009389192390353271/20000000000000000000 : ℝ) ≤ (2500287018651209/2500000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (20009389192390353271/20000000000000000000 : ℝ)^2048 ≤ (2500287018651209/2500000000000000 : ℝ)^8373 := by
      have hnat : (20009389192390353271 : ℕ)^2048*2500000000000000^8373 ≤ 2500287018651209^8373*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009389192390353271 20000000000000000000 2500287018651209 2500000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500287018651209/2500000000000000 : ℝ)) (X := (20009389192390353271/20000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254127591508653297/6250000000000000000 : ℝ) ≤ (2500403752629437/2500000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (6254127591508653297/6250000000000000000 : ℝ)^2048 ≤ (2500403752629437/2500000000000000 : ℝ)^8373 := by
      have hnat : (6254127591508653297 : ℕ)^2048*2500000000000000^8373 ≤ 2500403752629437^8373*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254127591508653297 6250000000000000000 2500403752629437 2500000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500403752629437/2500000000000000 : ℝ)) (X := (6254127591508653297/6250000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13925229882539979/100000000000000000000 : ℝ) ≤ ((418612220538991253/418750000000000000 : ℝ)+2*(29183494557/16750000000000 : ℝ)*(11397/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (418612220538991253/418750000000000000 : ℝ)+2*(29183494557/16750000000000 : ℝ)*(11397/100000 : ℝ)=(2500170284672981/2500000000000000 : ℝ) by norm_num, show 1+2*(13925229882539979/100000000000000000000 : ℝ)=(50013925229882539979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4127591508653297/12500000000000000000 : ℝ)+(13925229882539979/100000000000000000000 : ℝ) ≤ ((418612220538991253/418750000000000000 : ℝ)+(29183494557/16750000000000 : ℝ)*((14077/100000 : ℝ)+(11397/100000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (418612220538991253/418750000000000000 : ℝ)+(29183494557/16750000000000 : ℝ)*((14077/100000 : ℝ)+(11397/100000 : ℝ))=(2500287018651209/2500000000000000 : ℝ) by norm_num, show 1+(4127591508653297/12500000000000000000 : ℝ)+(13925229882539979/100000000000000000000 : ℝ)=(20009389192390353271/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4127591508653297/12500000000000000000 : ℝ) ≤ ((418612220538991253/418750000000000000 : ℝ)+2*(29183494557/16750000000000 : ℝ)*(14077/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (418612220538991253/418750000000000000 : ℝ)+2*(29183494557/16750000000000 : ℝ)*(14077/100000 : ℝ)=(2500403752629437/2500000000000000 : ℝ) by norm_num, show 1+2*(4127591508653297/12500000000000000000 : ℝ)=(6254127591508653297/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (418612220538991253/418750000000000000 : ℝ)*(X 1 0+X 2 0)+(29183494557/16750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (418612220538991253/418750000000000000 : ℝ)) (alpha := (29183494557/16750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (418612220538991253/418750000000000000 : ℝ)*(X 0 1+X 2 1)+(29183494557/16750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (418612220538991253/418750000000000000 : ℝ)) (alpha := (29183494557/16750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (418612220538991253/418750000000000000 : ℝ)*(X 0 2+X 1 2)+(29183494557/16750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (418612220538991253/418750000000000000 : ℝ)) (alpha := (29183494557/16750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2148374847/10000000000 : ℝ)*X 0 0+(1078467157/2000000000 : ℝ)*X 0 1+(5266336071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334037761/625000000 : ℝ)*X 1 0+(-553068653/2500000000 : ℝ)*X 1 1+(658292011/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068920837/2000000000 : ℝ)*X 2 0+(5266336081/10000000000 : ℝ)*X 2 1+(-2212274609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359207133/10000000000 : ℝ)*X 0 0+(52933939/125000000 : ℝ)*X 0 1+(280456703/625000000 : ℝ)*X 0 2+(4359207133/10000000000 : ℝ)*X 1 0+(52933939/125000000 : ℝ)*X 1 1+(280456703/625000000 : ℝ)*X 1 2+(4359207133/10000000000 : ℝ)*X 2 0+(52933939/125000000 : ℝ)*X 2 1+(280456703/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-537094911/2500000000 : ℝ)*X 0 0+(164582911/312500000 : ℝ)*X 0 1+(1078403511/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312590817/10000000000 : ℝ)*X 1 0+(-1043296569/5000000000 : ℝ)*X 1 1+(5392017557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062518163/2000000000 : ℝ)*X 2 0+(5392017559/10000000000 : ℝ)*X 2 1+(-2086593139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089804183/2500000000 : ℝ)*X 0 0+(4486671619/10000000000 : ℝ)*X 0 1+(529419133/1250000000 : ℝ)*X 0 2+(1089804183/2500000000 : ℝ)*X 1 0+(4486671619/10000000000 : ℝ)*X 1 1+(529419133/1250000000 : ℝ)*X 1 2+(1089804183/2500000000 : ℝ)*X 2 0+(4486671619/10000000000 : ℝ)*X 2 1+(529419133/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7213536474138557835309/1675000000000000000000000000 : ℝ) := by norm_num
    linear_combination (863262119/100000000000000 : ℝ)*(base19) + (201502499/25000000000000 : ℝ)*(base23) + (18870957/50000000000000 : ℝ)*(lower2) + (113275789/100000000000000 : ℝ)*(upper3) + (68305111/100000000000000 : ℝ)*(upper5) + (5947776059652423/100000000000000 : ℝ)*(major0) + (5947776059652423/100000000000000 : ℝ)*(major1) + (5947776059652423/100000000000000 : ℝ)*(major2) + (793655137902141/10000000000000 : ℝ)*(sp0) + (3968287545117809/50000000000000 : ℝ)*(sp1) + (7936575147487741/100000000000000 : ℝ)*(sp2) + (1979481536744343/50000000000000 : ℝ)*(sp3) + (3071809541/12500000000000 : ℝ)*(sp4) + (6474382723/50000000000000 : ℝ)*(sp7) + (3958976022254133/100000000000000 : ℝ)*(f.failure) + (7936575953497737/100000000000000 : ℝ)*(f.sum) + (6609687612411/837500000000000000000000000 : ℝ)*base65 + (488067350429968981/41875000000000000000000000000000 : ℝ)*base68 + (543773190663718981/41875000000000000000000000000000 : ℝ)*base70 + (374373726258718981/41875000000000000000000000000000 : ℝ)*base72 + (904168487491/209375000000000000000000000 : ℝ)*base74 + (217339932037531019/41875000000000000000000000000000 : ℝ)*base75 + (798207707341906019/41875000000000000000000000000000 : ℝ)*base77 + (437422898879406019/41875000000000000000000000000000 : ℝ)*base79 + (2976656098197/1675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (111385329/10000000000000000000000 : ℝ)*base89 + (111385329/10000000000000000000000 : ℝ)*base91 + (111385329/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33140346492805000398326409/4187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288285347/20000000000000 : ℝ)*(base19) + (1562704739/100000000000000 : ℝ)*(base23) + (160474433/100000000000000 : ℝ)*(upper3) + (56621033/100000000000000 : ℝ)*(lower4) + (10152883/6250000000000 : ℝ)*(upper5) + (1195575801318351/20000000000000 : ℝ)*(major0) + (1195575801318351/20000000000000 : ℝ)*(major1) + (1195575801318351/20000000000000 : ℝ)*(major2) + (2512939201/6250000000000 : ℝ)*(sp1) + (43144647571/100000000000000 : ℝ)*(sp2) + (498546532244779/6250000000000 : ℝ)*(sp4) + (498543929216407/6250000000000 : ℝ)*(sp5) + (1595339961712831/20000000000000 : ℝ)*(sp6) + (1989506616731643/50000000000000 : ℝ)*(sp7) + (1989506616731643/50000000000000 : ℝ)*(f.failure) + (498546532244779/6250000000000 : ℝ)*(f.sum) + (544211590727/167500000000000000000000000 : ℝ)*base65 + (30249520488308803/8375000000000000000000000000000 : ℝ)*base67 + (29068588330941197/8375000000000000000000000000000 : ℝ)*base70 + (73579818192058803/8375000000000000000000000000000 : ℝ)*base71 + (200477828287/41875000000000000000000000 : ℝ)*base74 + (1940025958941197/8375000000000000000000000000000 : ℝ)*base76 + (43550541917941197/8375000000000000000000000000000 : ℝ)*base78 + (122426833093691197/8375000000000000000000000000000 : ℝ)*base80 + (707617830343/167500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (55041/5000000000000000000000 : ℝ)*base90 + (55041/5000000000000000000000 : ℝ)*base92 + (55041/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1181_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1181_s8_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13427347/62500000 : ℝ)*x 0 + (2696141917/5000000000 : ℝ)*x 1 + (5266387919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13427347/62500000 : ℝ)^4187 ≤ (13058261393749/100000000000000 : ℝ)^3163 := by
    have hnat : (13427347 : ℕ)^4187*100000000000000^3163 ≤ 13058261393749^3163*62500000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13427347 62500000 13058261393749 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696141917/5000000000 : ℝ)^4187 ≤ (551881689393/1250000000000 : ℝ)^3163 := by
    have hnat : (2696141917 : ℕ)^4187*1250000000000^3163 ≤ 551881689393^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696141917 5000000000 551881689393 1250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266387919/10000000000 : ℝ)^4187 ≤ (8558240689283/20000000000000 : ℝ)^3163 := by
    have hnat : (5266387919 : ℕ)^4187*20000000000000^3163 ≤ 8558240689283^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266387919 10000000000 8558240689283 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13427347/62500000 : ℝ), (2696141917/5000000000 : ℝ), (5266387919/10000000000 : ℝ)] ![(13058261393749/100000000000000 : ℝ), (551881689393/1250000000000 : ℝ), (8558240689283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13427347/62500000 : ℝ)|^4187 ≤ (13058261393749/100000000000000 : ℝ)^3163
        have hw : |(-13427347/62500000 : ℝ)|=(13427347/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696141917/5000000000 : ℝ)|^4187 ≤ (551881689393/1250000000000 : ℝ)^3163
        have hw : |(2696141917/5000000000 : ℝ)|=(2696141917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266387919/10000000000 : ℝ)|^4187 ≤ (8558240689283/20000000000000 : ℝ)^3163
        have hw : |(5266387919/10000000000 : ℝ)|=(5266387919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672296109/5000000000 : ℝ)*x 0 + (-2212221953/10000000000 : ℝ)*x 1 + (5266387871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672296109/5000000000 : ℝ)^4187 ≤ (5454296710323/12500000000000 : ℝ)^3163 := by
    have hnat : (2672296109 : ℕ)^4187*12500000000000^3163 ≤ 5454296710323^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672296109 5000000000 5454296710323 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212221953/10000000000 : ℝ)^4187 ≤ (1696802921551/12500000000000 : ℝ)^3163 := by
    have hnat : (2212221953 : ℕ)^4187*12500000000000^3163 ≤ 1696802921551^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212221953 10000000000 1696802921551 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266387871/10000000000 : ℝ)^4187 ≤ (42791202930133/100000000000000 : ℝ)^3163 := by
    have hnat : (5266387871 : ℕ)^4187*100000000000000^3163 ≤ 42791202930133^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266387871 10000000000 42791202930133 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672296109/5000000000 : ℝ), (-2212221953/10000000000 : ℝ), (5266387871/10000000000 : ℝ)] ![(5454296710323/12500000000000 : ℝ), (1696802921551/12500000000000 : ℝ), (42791202930133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672296109/5000000000 : ℝ)|^4187 ≤ (5454296710323/12500000000000 : ℝ)^3163
        have hw : |(2672296109/5000000000 : ℝ)|=(2672296109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212221953/10000000000 : ℝ)|^4187 ≤ (1696802921551/12500000000000 : ℝ)^3163
        have hw : |(-2212221953/10000000000 : ℝ)|=(2212221953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266387871/10000000000 : ℝ)|^4187 ≤ (42791202930133/100000000000000 : ℝ)^3163
        have hw : |(5266387871/10000000000 : ℝ)|=(5266387871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068918437/2000000000 : ℝ)*x 0 + (2633193951/5000000000 : ℝ)*x 1 + (-553055489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068918437/2000000000 : ℝ)^4187 ≤ (43634373325943/100000000000000 : ℝ)^3163 := by
    have hnat : (1068918437 : ℕ)^4187*100000000000000^3163 ≤ 43634373325943^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068918437 2000000000 43634373325943 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633193951/5000000000 : ℝ)^4187 ≤ (8558240652713/20000000000000 : ℝ)^3163 := by
    have hnat : (2633193951 : ℕ)^4187*20000000000000^3163 ≤ 8558240652713^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633193951 5000000000 8558240652713 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553055489/2500000000 : ℝ)^4187 ≤ (1696802924597/12500000000000 : ℝ)^3163 := by
    have hnat : (553055489 : ℕ)^4187*12500000000000^3163 ≤ 1696802924597^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553055489 2500000000 1696802924597 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068918437/2000000000 : ℝ), (2633193951/5000000000 : ℝ), (-553055489/2500000000 : ℝ)] ![(43634373325943/100000000000000 : ℝ), (8558240652713/20000000000000 : ℝ), (1696802924597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068918437/2000000000 : ℝ)|^4187 ≤ (43634373325943/100000000000000 : ℝ)^3163
        have hw : |(1068918437/2000000000 : ℝ)|=(1068918437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633193951/5000000000 : ℝ)|^4187 ≤ (8558240652713/20000000000000 : ℝ)^3163
        have hw : |(2633193951/5000000000 : ℝ)|=(2633193951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553055489/2500000000 : ℝ)|^4187 ≤ (1696802924597/12500000000000 : ℝ)^3163
        have hw : |(-553055489/2500000000 : ℝ)|=(553055489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359209707/10000000000 : ℝ)*x 0 + (4234818807/10000000000 : ℝ)*x 1 + (4487202937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359209707/10000000000 : ℝ)^4187 ≤ (16658598144131/50000000000000 : ℝ)^3163 := by
    have hnat : (4359209707 : ℕ)^4187*50000000000000^3163 ≤ 16658598144131^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359209707 10000000000 16658598144131 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234818807/10000000000 : ℝ)^4187 ≤ (32064547642583/100000000000000 : ℝ)^3163 := by
    have hnat : (4234818807 : ℕ)^4187*100000000000000^3163 ≤ 32064547642583^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234818807 10000000000 32064547642583 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487202937/10000000000 : ℝ)^4187 ≤ (4327282007263/12500000000000 : ℝ)^3163 := by
    have hnat : (4487202937 : ℕ)^4187*12500000000000^3163 ≤ 4327282007263^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487202937 10000000000 4327282007263 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359209707/10000000000 : ℝ), (4234818807/10000000000 : ℝ), (4487202937/10000000000 : ℝ)] ![(16658598144131/50000000000000 : ℝ), (32064547642583/100000000000000 : ℝ), (4327282007263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359209707/10000000000 : ℝ)|^4187 ≤ (16658598144131/50000000000000 : ℝ)^3163
        have hw : |(4359209707/10000000000 : ℝ)|=(4359209707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234818807/10000000000 : ℝ)|^4187 ≤ (32064547642583/100000000000000 : ℝ)^3163
        have hw : |(4234818807/10000000000 : ℝ)|=(4234818807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487202937/10000000000 : ℝ)|^4187 ≤ (4327282007263/12500000000000 : ℝ)^3163
        have hw : |(4487202937/10000000000 : ℝ)|=(4487202937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148380573/10000000000 : ℝ)*x 0 + (21066819/40000000 : ℝ)*x 1 + (5391965659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148380573/10000000000 : ℝ)^4187 ≤ (13058302050099/100000000000000 : ℝ)^3163 := by
    have hnat : (2148380573 : ℕ)^4187*100000000000000^3163 ≤ 13058302050099^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148380573 10000000000 13058302050099 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21066819/40000000 : ℝ)^4187 ≤ (42794611271701/100000000000000 : ℝ)^3163 := by
    have hnat : (21066819 : ℕ)^4187*100000000000000^3163 ≤ 42794611271701^3163*40000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21066819 40000000 42794611271701 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391965659/10000000000 : ℝ)^4187 ≤ (5518385832749/12500000000000 : ℝ)^3163 := by
    have hnat : (5391965659 : ℕ)^4187*12500000000000^3163 ≤ 5518385832749^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391965659 10000000000 5518385832749 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148380573/10000000000 : ℝ), (21066819/40000000 : ℝ), (5391965659/10000000000 : ℝ)] ![(13058302050099/100000000000000 : ℝ), (42794611271701/100000000000000 : ℝ), (5518385832749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148380573/10000000000 : ℝ)|^4187 ≤ (13058302050099/100000000000000 : ℝ)^3163
        have hw : |(-2148380573/10000000000 : ℝ)|=(2148380573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21066819/40000000 : ℝ)|^4187 ≤ (42794611271701/100000000000000 : ℝ)^3163
        have hw : |(21066819/40000000 : ℝ)|=(21066819/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391965659/10000000000 : ℝ)|^4187 ≤ (5518385832749/12500000000000 : ℝ)^3163
        have hw : |(5391965659/10000000000 : ℝ)|=(5391965659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42500841/80000000 : ℝ)*x 0 + (-2086643443/10000000000 : ℝ)*x 1 + (1347991581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42500841/80000000 : ℝ)^4187 ≤ (21644507174103/50000000000000 : ℝ)^3163 := by
    have hnat : (42500841 : ℕ)^4187*50000000000000^3163 ≤ 21644507174103^3163*80000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42500841 80000000 21644507174103 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086643443/10000000000 : ℝ)^4187 ≤ (6281945882851/50000000000000 : ℝ)^3163 := by
    have hnat : (2086643443 : ℕ)^4187*50000000000000^3163 ≤ 6281945882851^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086643443 10000000000 6281945882851 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347991581/2500000000 : ℝ)^4187 ≤ (2207354693471/5000000000000 : ℝ)^3163 := by
    have hnat : (1347991581 : ℕ)^4187*5000000000000^3163 ≤ 2207354693471^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347991581 2500000000 2207354693471 5000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42500841/80000000 : ℝ), (-2086643443/10000000000 : ℝ), (1347991581/2500000000 : ℝ)] ![(21644507174103/50000000000000 : ℝ), (6281945882851/50000000000000 : ℝ), (2207354693471/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42500841/80000000 : ℝ)|^4187 ≤ (21644507174103/50000000000000 : ℝ)^3163
        have hw : |(42500841/80000000 : ℝ)|=(42500841/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086643443/10000000000 : ℝ)|^4187 ≤ (6281945882851/50000000000000 : ℝ)^3163
        have hw : |(-2086643443/10000000000 : ℝ)|=(2086643443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347991581/2500000000 : ℝ)|^4187 ≤ (2207354693471/5000000000000 : ℝ)^3163
        have hw : |(1347991581/2500000000 : ℝ)|=(1347991581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062521091/2000000000 : ℝ)*x 0 + (2695982911/5000000000 : ℝ)*x 1 + (-13041523/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062521091/2000000000 : ℝ)^4187 ≤ (43289017907697/100000000000000 : ℝ)^3163 := by
    have hnat : (1062521091 : ℕ)^4187*100000000000000^3163 ≤ 43289017907697^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062521091 2000000000 43289017907697 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695982911/5000000000 : ℝ)^4187 ≤ (2759193026789/6250000000000 : ℝ)^3163 := by
    have hnat : (2695982911 : ℕ)^4187*6250000000000^3163 ≤ 2759193026789^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695982911 5000000000 2759193026789 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13041523/62500000 : ℝ)^4187 ≤ (2512778730937/20000000000000 : ℝ)^3163 := by
    have hnat : (13041523 : ℕ)^4187*20000000000000^3163 ≤ 2512778730937^3163*62500000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13041523 62500000 2512778730937 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062521091/2000000000 : ℝ), (2695982911/5000000000 : ℝ), (-13041523/62500000 : ℝ)] ![(43289017907697/100000000000000 : ℝ), (2759193026789/6250000000000 : ℝ), (2512778730937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062521091/2000000000 : ℝ)|^4187 ≤ (43289017907697/100000000000000 : ℝ)^3163
        have hw : |(1062521091/2000000000 : ℝ)|=(1062521091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695982911/5000000000 : ℝ)|^4187 ≤ (2759193026789/6250000000000 : ℝ)^3163
        have hw : |(2695982911/5000000000 : ℝ)|=(2695982911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13041523/62500000 : ℝ)|^4187 ≤ (2512778730937/20000000000000 : ℝ)^3163
        have hw : |(-13041523/62500000 : ℝ)|=(13041523/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s8_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359219171/10000000000 : ℝ)*x 0 + (2243284249/5000000000 : ℝ)*x 1 + (847091133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359219171/10000000000 : ℝ)^4187 ≤ (2082330752399/6250000000000 : ℝ)^3163 := by
    have hnat : (4359219171 : ℕ)^4187*6250000000000^3163 ≤ 2082330752399^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359219171 10000000000 2082330752399 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243284249/5000000000 : ℝ)^4187 ≤ (34611776980593/100000000000000 : ℝ)^3163 := by
    have hnat : (2243284249 : ℕ)^4187*100000000000000^3163 ≤ 34611776980593^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243284249 5000000000 34611776980593 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847091133/2000000000 : ℝ)^4187 ≤ (32070930971653/100000000000000 : ℝ)^3163 := by
    have hnat : (847091133 : ℕ)^4187*100000000000000^3163 ≤ 32070930971653^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847091133 2000000000 32070930971653 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359219171/10000000000 : ℝ), (2243284249/5000000000 : ℝ), (847091133/2000000000 : ℝ)] ![(2082330752399/6250000000000 : ℝ), (34611776980593/100000000000000 : ℝ), (32070930971653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359219171/10000000000 : ℝ)|^4187 ≤ (2082330752399/6250000000000 : ℝ)^3163
        have hw : |(4359219171/10000000000 : ℝ)|=(4359219171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243284249/5000000000 : ℝ)|^4187 ≤ (34611776980593/100000000000000 : ℝ)^3163
        have hw : |(2243284249/5000000000 : ℝ)|=(2243284249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847091133/2000000000 : ℝ)|^4187 ≤ (32070930971653/100000000000000 : ℝ)^3163
        have hw : |(847091133/2000000000 : ℝ)|=(847091133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2851/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11403/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (13955226152803617/100000000000000000000 : ℝ) := by
    have hpowers : (11403/100000 : ℝ)^8373 ≤ (13955226152803617/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11403 : ℕ)^8373*100000000000000000000^2048 ≤ 13955226152803617^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11403 100000 13955226152803617 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11403/100000 : ℝ)) (X := (13955226152803617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1759/12500 : ℝ) ^ (8373/2048 : ℝ) ≤ (32972807356102737/100000000000000000000 : ℝ) := by
    have hpowers : (1759/12500 : ℝ)^8373 ≤ (32972807356102737/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1759 : ℕ)^8373*100000000000000000000^2048 ≤ 32972807356102737^2048*12500^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 12500 32972807356102737 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/12500 : ℝ)) (X := (32972807356102737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013955226152803617/50000000000000000000 : ℝ) ≤ (10000682605774843/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50013955226152803617/50000000000000000000 : ℝ)^2048 ≤ (10000682605774843/10000000000000000 : ℝ)^8373 := by
      have hnat : (50013955226152803617 : ℕ)^2048*10000000000000000^8373 ≤ 10000682605774843^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013955226152803617 50000000000000000000 10000682605774843 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682605774843/10000000000000000 : ℝ)) (X := (50013955226152803617/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023464016754453177/50000000000000000000 : ℝ) ≤ (10001147636238209/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50023464016754453177/50000000000000000000 : ℝ)^2048 ≤ (10001147636238209/10000000000000000 : ℝ)^8373 := by
      have hnat : (50023464016754453177 : ℕ)^2048*10000000000000000^8373 ≤ 10001147636238209^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023464016754453177 50000000000000000000 10001147636238209 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001147636238209/10000000000000000 : ℝ)) (X := (50023464016754453177/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032972807356102737/50000000000000000000 : ℝ) ≤ (400064506668063/400000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50032972807356102737/50000000000000000000 : ℝ)^2048 ≤ (400064506668063/400000000000000 : ℝ)^8373 := by
      have hnat : (50032972807356102737 : ℕ)^2048*400000000000000^8373 ≤ 400064506668063^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032972807356102737 50000000000000000000 400064506668063 400000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400064506668063/400000000000000 : ℝ)) (X := (50032972807356102737/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13955226152803617/100000000000000000000 : ℝ) ≤ ((26681216390065530971/26690000000000000000 : ℝ)+2*(232515231683/133450000000000 : ℝ)*(11403/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (26681216390065530971/26690000000000000000 : ℝ)+2*(232515231683/133450000000000 : ℝ)*(11403/100000 : ℝ)=(10000682605774843/10000000000000000 : ℝ) by norm_num, show 1+2*(13955226152803617/100000000000000000000 : ℝ)=(50013955226152803617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32972807356102737/100000000000000000000 : ℝ)+(13955226152803617/100000000000000000000 : ℝ) ≤ ((26681216390065530971/26690000000000000000 : ℝ)+(232515231683/133450000000000 : ℝ)*((1759/12500 : ℝ)+(11403/100000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (26681216390065530971/26690000000000000000 : ℝ)+(232515231683/133450000000000 : ℝ)*((1759/12500 : ℝ)+(11403/100000 : ℝ))=(10001147636238209/10000000000000000 : ℝ) by norm_num, show 1+(32972807356102737/100000000000000000000 : ℝ)+(13955226152803617/100000000000000000000 : ℝ)=(50023464016754453177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32972807356102737/100000000000000000000 : ℝ) ≤ ((26681216390065530971/26690000000000000000 : ℝ)+2*(232515231683/133450000000000 : ℝ)*(1759/12500 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (26681216390065530971/26690000000000000000 : ℝ)+2*(232515231683/133450000000000 : ℝ)*(1759/12500 : ℝ)=(400064506668063/400000000000000 : ℝ) by norm_num, show 1+2*(32972807356102737/100000000000000000000 : ℝ)=(50032972807356102737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26681216390065530971/26690000000000000000 : ℝ)*(X 1 0+X 2 0)+(232515231683/133450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (26681216390065530971/26690000000000000000 : ℝ)) (alpha := (232515231683/133450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26681216390065530971/26690000000000000000 : ℝ)*(X 0 1+X 2 1)+(232515231683/133450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (26681216390065530971/26690000000000000000 : ℝ)) (alpha := (232515231683/133450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26681216390065530971/26690000000000000000 : ℝ)*(X 0 2+X 1 2)+(232515231683/133450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (26681216390065530971/26690000000000000000 : ℝ)) (alpha := (232515231683/133450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13427347/62500000 : ℝ)*X 0 0+(2696141917/5000000000 : ℝ)*X 0 1+(5266387919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672296109/5000000000 : ℝ)*X 1 0+(-2212221953/10000000000 : ℝ)*X 1 1+(5266387871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068918437/2000000000 : ℝ)*X 2 0+(2633193951/5000000000 : ℝ)*X 2 1+(-553055489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359209707/10000000000 : ℝ)*X 0 0+(4234818807/10000000000 : ℝ)*X 0 1+(4487202937/10000000000 : ℝ)*X 0 2+(4359209707/10000000000 : ℝ)*X 1 0+(4234818807/10000000000 : ℝ)*X 1 1+(4487202937/10000000000 : ℝ)*X 1 2+(4359209707/10000000000 : ℝ)*X 2 0+(4234818807/10000000000 : ℝ)*X 2 1+(4487202937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2148380573/10000000000 : ℝ)*X 0 0+(21066819/40000000 : ℝ)*X 0 1+(5391965659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42500841/80000000 : ℝ)*X 1 0+(-2086643443/10000000000 : ℝ)*X 1 1+(1347991581/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062521091/2000000000 : ℝ)*X 2 0+(2695982911/5000000000 : ℝ)*X 2 1+(-13041523/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359219171/10000000000 : ℝ)*X 0 0+(2243284249/5000000000 : ℝ)*X 0 1+(847091133/2000000000 : ℝ)*X 0 2+(4359219171/10000000000 : ℝ)*X 1 0+(2243284249/5000000000 : ℝ)*X 1 1+(847091133/2000000000 : ℝ)*X 1 2+(4359219171/10000000000 : ℝ)*X 2 0+(2243284249/5000000000 : ℝ)*X 2 1+(847091133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105785937791865858693898959/19625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1032811439/100000000000000 : ℝ)*(base19) + (915190307/100000000000000 : ℝ)*(base23) + (286339/781250000000 : ℝ)*(lower2) + (63410123/50000000000000 : ℝ)*(upper3) + (31245063/50000000000000 : ℝ)*(upper5) + (2976341484645969/50000000000000 : ℝ)*(major0) + (2976341484645969/50000000000000 : ℝ)*(major1) + (2976341484645969/50000000000000 : ℝ)*(major2) + (1588619557748873/20000000000000 : ℝ)*(sp0) + (1985780638088751/25000000000000 : ℝ)*(sp1) + (1588624533995227/20000000000000 : ℝ)*(sp2) + (990556867575273/25000000000000 : ℝ)*(sp3) + (12898211039/50000000000000 : ℝ)*(sp4) + (918964841/6250000000000 : ℝ)*(sp7) + (990560543434637/25000000000000 : ℝ)*(f.failure) + (7943123585166443/100000000000000 : ℝ)*(f.sum) + (17519923619419/6672500000000000000000000000 : ℝ)*base65 + (3943770518156205899/1334500000000000000000000000000000 : ℝ)*base67 + (3944334959610705899/1334500000000000000000000000000000 : ℝ)*base69 + (12529324777231205899/1334500000000000000000000000000000 : ℝ)*base71 + (15903473142773/3336250000000000000000000000 : ℝ)*base74 + (33448781251189205899/1334500000000000000000000000000000 : ℝ)*base75 + (5227193397222294101/1334500000000000000000000000000000 : ℝ)*base78 + (19641290026486205899/1334500000000000000000000000000000 : ℝ)*base79 + (12844393035957/3336250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8727319/2500000000000000000000 : ℝ)*base90 + (8727319/2500000000000000000000 : ℝ)*base92 + (8727319/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86111478475208734760943/13345000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177979833/10000000000000 : ℝ)*(base19) + (2786970553/100000000000000 : ℝ)*(base23) + (474649179/50000000000000 : ℝ)*(lower1) + (44176439/20000000000000 : ℝ)*(upper2) + (401724137/100000000000000 : ℝ)*(upper3) + (747843308581293/12500000000000 : ℝ)*(major0) + (747843308581293/12500000000000 : ℝ)*(major1) + (747843308581293/12500000000000 : ℝ)*(major2) + (396584937/2500000000000 : ℝ)*(sp2) + (84325693/2000000000000 : ℝ)*(sp3) + (399161979723809/5000000000000 : ℝ)*(sp4) + (159664756293557/2000000000000 : ℝ)*(sp5) + (7983220944108147/100000000000000 : ℝ)*(sp6) + (1991124455724677/50000000000000 : ℝ)*(sp7) + (995563281933501/25000000000000 : ℝ)*(f.failure) + (399161979723809/5000000000000 : ℝ)*(f.sum) + (6267268363153/1668125000000000000000000000 : ℝ)*base65 + (1212928280949275503/333625000000000000000000000000000 : ℝ)*base67 + (1920315958046525503/333625000000000000000000000000000 : ℝ)*base69 + (1331671794944224497/333625000000000000000000000000000 : ℝ)*base72 + (544275055959/3336250000000000000000000000 : ℝ)*base74 + (5237682074680974497/333625000000000000000000000000000 : ℝ)*base76 + (374868644178900503/333625000000000000000000000000000 : ℝ)*base77 + (9869154662323974497/333625000000000000000000000000000 : ℝ)*base80 + (17877328662251/3336250000000000000000000000 : ℝ)*base81 + (25429287/2500000000000000000000 : ℝ)*base90 + (25429287/2500000000000000000000 : ℝ)*base92 + (25429287/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1181_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1181_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1181_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1181_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1181_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

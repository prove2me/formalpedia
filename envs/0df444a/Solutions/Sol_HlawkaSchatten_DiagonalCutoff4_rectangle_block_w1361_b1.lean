-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1361_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:01.247048+00:00
-- url     : https://prove2.me/submissions/516c5f0b-4af5-4036-a09c-2a9c7f7627e2

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
theorem support_rectangle_w1361_s3_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026094339/10000000000 : ℝ)*x 0 + (1084961357/2000000000 : ℝ)*x 1 + (523312887/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026094339/10000000000 : ℝ)^4321 ≤ (12340088963257/100000000000000 : ℝ)^3297 := by
    have hnat : (2026094339 : ℕ)^4321*100000000000000^3297 ≤ 12340088963257^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026094339 10000000000 12340088963257 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084961357/2000000000 : ℝ)^4321 ≤ (1401967464439/3125000000000 : ℝ)^3297 := by
    have hnat : (1084961357 : ℕ)^4321*3125000000000^3297 ≤ 1401967464439^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084961357 2000000000 1401967464439 3125000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523312887/1000000000 : ℝ)^4321 ≤ (21398476082183/50000000000000 : ℝ)^3297 := by
    have hnat : (523312887 : ℕ)^4321*50000000000000^3297 ≤ 21398476082183^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523312887 1000000000 21398476082183 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026094339/10000000000 : ℝ), (1084961357/2000000000 : ℝ), (523312887/1000000000 : ℝ)] ![(12340088963257/100000000000000 : ℝ), (1401967464439/3125000000000 : ℝ), (21398476082183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026094339/10000000000 : ℝ)|^4321 ≤ (12340088963257/100000000000000 : ℝ)^3297
        have hw : |(-2026094339/10000000000 : ℝ)|=(2026094339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084961357/2000000000 : ℝ)|^4321 ≤ (1401967464439/3125000000000 : ℝ)^3297
        have hw : |(1084961357/2000000000 : ℝ)|=(1084961357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523312887/1000000000 : ℝ)|^4321 ≤ (21398476082183/50000000000000 : ℝ)^3297
        have hw : |(523312887/1000000000 : ℝ)|=(523312887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214080273/400000000 : ℝ)*x 0 + (-2124010739/10000000000 : ℝ)*x 1 + (654141107/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214080273/400000000 : ℝ)^4321 ≤ (44075566366647/100000000000000 : ℝ)^3297 := by
    have hnat : (214080273 : ℕ)^4321*100000000000000^3297 ≤ 44075566366647^3297*400000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214080273 400000000 44075566366647 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124010739/10000000000 : ℝ)^4321 ≤ (13127481602261/100000000000000 : ℝ)^3297 := by
    have hnat : (2124010739 : ℕ)^4321*100000000000000^3297 ≤ 13127481602261^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124010739 10000000000 13127481602261 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654141107/1250000000 : ℝ)^4321 ≤ (42796952014313/100000000000000 : ℝ)^3297 := by
    have hnat : (654141107 : ℕ)^4321*100000000000000^3297 ≤ 42796952014313^3297*1250000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654141107 1250000000 42796952014313 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214080273/400000000 : ℝ), (-2124010739/10000000000 : ℝ), (654141107/1250000000 : ℝ)] ![(44075566366647/100000000000000 : ℝ), (13127481602261/100000000000000 : ℝ), (42796952014313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214080273/400000000 : ℝ)|^4321 ≤ (44075566366647/100000000000000 : ℝ)^3297
        have hw : |(214080273/400000000 : ℝ)|=(214080273/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124010739/10000000000 : ℝ)|^4321 ≤ (13127481602261/100000000000000 : ℝ)^3297
        have hw : |(-2124010739/10000000000 : ℝ)|=(2124010739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654141107/1250000000 : ℝ)|^4321 ≤ (42796952014313/100000000000000 : ℝ)^3297
        have hw : |(654141107/1250000000 : ℝ)|=(654141107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070401433/2000000000 : ℝ)*x 0 + (2616564217/5000000000 : ℝ)*x 1 + (-531002711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070401433/2000000000 : ℝ)^4321 ≤ (2754723127269/6250000000000 : ℝ)^3297 := by
    have hnat : (1070401433 : ℕ)^4321*6250000000000^3297 ≤ 2754723127269^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070401433 2000000000 2754723127269 6250000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616564217/5000000000 : ℝ)^4321 ≤ (21398473745643/50000000000000 : ℝ)^3297 := by
    have hnat : (2616564217 : ℕ)^4321*50000000000000^3297 ≤ 21398473745643^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616564217 5000000000 21398473745643 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531002711/2500000000 : ℝ)^4321 ≤ (13127482452771/100000000000000 : ℝ)^3297 := by
    have hnat : (531002711 : ℕ)^4321*100000000000000^3297 ≤ 13127482452771^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531002711 2500000000 13127482452771 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070401433/2000000000 : ℝ), (2616564217/5000000000 : ℝ), (-531002711/2500000000 : ℝ)] ![(2754723127269/6250000000000 : ℝ), (21398473745643/50000000000000 : ℝ), (13127482452771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070401433/2000000000 : ℝ)|^4321 ≤ (2754723127269/6250000000000 : ℝ)^3297
        have hw : |(1070401433/2000000000 : ℝ)|=(1070401433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616564217/5000000000 : ℝ)|^4321 ≤ (21398473745643/50000000000000 : ℝ)^3297
        have hw : |(2616564217/5000000000 : ℝ)|=(2616564217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531002711/2500000000 : ℝ)|^4321 ≤ (13127482452771/100000000000000 : ℝ)^3297
        have hw : |(-531002711/2500000000 : ℝ)|=(531002711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320722199/10000000000 : ℝ)*x 0 + (25768269/62500000 : ℝ)*x 1 + (4527279007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320722199/10000000000 : ℝ)^4321 ≤ (104043629611/312500000000 : ℝ)^3297 := by
    have hnat : (4320722199 : ℕ)^4321*312500000000^3297 ≤ 104043629611^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320722199 10000000000 104043629611 312500000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25768269/62500000 : ℝ)^4321 ≤ (31310759149783/100000000000000 : ℝ)^3297 := by
    have hnat : (25768269 : ℕ)^4321*100000000000000^3297 ≤ 31310759149783^3297*62500000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25768269 62500000 31310759149783 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527279007/10000000000 : ℝ)^4321 ≤ (35395279361481/100000000000000 : ℝ)^3297 := by
    have hnat : (4527279007 : ℕ)^4321*100000000000000^3297 ≤ 35395279361481^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527279007 10000000000 35395279361481 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320722199/10000000000 : ℝ), (25768269/62500000 : ℝ), (4527279007/10000000000 : ℝ)] ![(104043629611/312500000000 : ℝ), (31310759149783/100000000000000 : ℝ), (35395279361481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320722199/10000000000 : ℝ)|^4321 ≤ (104043629611/312500000000 : ℝ)^3297
        have hw : |(4320722199/10000000000 : ℝ)|=(4320722199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25768269/62500000 : ℝ)|^4321 ≤ (31310759149783/100000000000000 : ℝ)^3297
        have hw : |(25768269/62500000 : ℝ)|=(25768269/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527279007/10000000000 : ℝ)|^4321 ≤ (35395279361481/100000000000000 : ℝ)^3297
        have hw : |(4527279007/10000000000 : ℝ)|=(4527279007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101305671/500000000 : ℝ)*x 0 + (327119927/625000000 : ℝ)*x 1 + (542401151/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101305671/500000000 : ℝ)^4321 ≤ (12340241272309/100000000000000 : ℝ)^3297 := by
    have hnat : (101305671 : ℕ)^4321*100000000000000^3297 ≤ 12340241272309^3297*500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101305671 500000000 12340241272309 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327119927/625000000 : ℝ)^4321 ≤ (8561083846723/20000000000000 : ℝ)^3297 := by
    have hnat : (327119927 : ℕ)^4321*20000000000000^3297 ≤ 8561083846723^3297*625000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327119927 625000000 8561083846723 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542401151/1000000000 : ℝ)^4321 ≤ (8970867894929/20000000000000 : ℝ)^3297 := by
    have hnat : (542401151 : ℕ)^4321*20000000000000^3297 ≤ 8970867894929^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542401151 1000000000 8970867894929 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101305671/500000000 : ℝ), (327119927/625000000 : ℝ), (542401151/1000000000 : ℝ)] ![(12340241272309/100000000000000 : ℝ), (8561083846723/20000000000000 : ℝ), (8970867894929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101305671/500000000 : ℝ)|^4321 ≤ (12340241272309/100000000000000 : ℝ)^3297
        have hw : |(-101305671/500000000 : ℝ)|=(101305671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327119927/625000000 : ℝ)|^4321 ≤ (8561083846723/20000000000000 : ℝ)^3297
        have hw : |(327119927/625000000 : ℝ)|=(327119927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542401151/1000000000 : ℝ)|^4321 ≤ (8970867894929/20000000000000 : ℝ)^3297
        have hw : |(542401151/1000000000 : ℝ)|=(542401151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651263827/5000000000 : ℝ)*x 0 + (-1933127851/10000000000 : ℝ)*x 1 + (5424012039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651263827/5000000000 : ℝ)^4321 ≤ (43542300617583/100000000000000 : ℝ)^3297 := by
    have hnat : (2651263827 : ℕ)^4321*100000000000000^3297 ≤ 43542300617583^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651263827 5000000000 43542300617583 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933127851/10000000000 : ℝ)^4321 ≤ (11603354151039/100000000000000 : ℝ)^3297 := by
    have hnat : (1933127851 : ℕ)^4321*100000000000000^3297 ≤ 11603354151039^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933127851 10000000000 11603354151039 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424012039/10000000000 : ℝ)^4321 ≤ (44854345207947/100000000000000 : ℝ)^3297 := by
    have hnat : (5424012039 : ℕ)^4321*100000000000000^3297 ≤ 44854345207947^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424012039 10000000000 44854345207947 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651263827/5000000000 : ℝ), (-1933127851/10000000000 : ℝ), (5424012039/10000000000 : ℝ)] ![(43542300617583/100000000000000 : ℝ), (11603354151039/100000000000000 : ℝ), (44854345207947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651263827/5000000000 : ℝ)|^4321 ≤ (43542300617583/100000000000000 : ℝ)^3297
        have hw : |(2651263827/5000000000 : ℝ)|=(2651263827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933127851/10000000000 : ℝ)|^4321 ≤ (11603354151039/100000000000000 : ℝ)^3297
        have hw : |(-1933127851/10000000000 : ℝ)|=(1933127851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424012039/10000000000 : ℝ)|^4321 ≤ (44854345207947/100000000000000 : ℝ)^3297
        have hw : |(5424012039/10000000000 : ℝ)|=(5424012039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060505759/2000000000 : ℝ)*x 0 + (678001407/1250000000 : ℝ)*x 1 + (-193312737/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060505759/2000000000 : ℝ)^4321 ≤ (43542312897047/100000000000000 : ℝ)^3297 := by
    have hnat : (1060505759 : ℕ)^4321*100000000000000^3297 ≤ 43542312897047^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060505759 2000000000 43542312897047 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678001407/1250000000 : ℝ)^4321 ≤ (350424505639/781250000000 : ℝ)^3297 := by
    have hnat : (678001407 : ℕ)^4321*781250000000^3297 ≤ 350424505639^3297*1250000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678001407 1250000000 350424505639 781250000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193312737/1000000000 : ℝ)^4321 ≤ (5801675183597/50000000000000 : ℝ)^3297 := by
    have hnat : (193312737 : ℕ)^4321*50000000000000^3297 ≤ 5801675183597^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193312737 1000000000 5801675183597 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060505759/2000000000 : ℝ), (678001407/1250000000 : ℝ), (-193312737/1000000000 : ℝ)] ![(43542312897047/100000000000000 : ℝ), (350424505639/781250000000 : ℝ), (5801675183597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060505759/2000000000 : ℝ)|^4321 ≤ (43542312897047/100000000000000 : ℝ)^3297
        have hw : |(1060505759/2000000000 : ℝ)|=(1060505759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678001407/1250000000 : ℝ)|^4321 ≤ (350424505639/781250000000 : ℝ)^3297
        have hw : |(678001407/1250000000 : ℝ)|=(678001407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193312737/1000000000 : ℝ)|^4321 ≤ (5801675183597/50000000000000 : ℝ)^3297
        have hw : |(-193312737/1000000000 : ℝ)|=(193312737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320760231/10000000000 : ℝ)*x 0 + (4525611939/10000000000 : ℝ)*x 1 + (2062300233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320760231/10000000000 : ℝ)^4321 ≤ (33294345557743/100000000000000 : ℝ)^3297 := by
    have hnat : (4320760231 : ℕ)^4321*100000000000000^3297 ≤ 33294345557743^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320760231 10000000000 33294345557743 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525611939/10000000000 : ℝ)^4321 ≤ (35378198810277/100000000000000 : ℝ)^3297 := by
    have hnat : (4525611939 : ℕ)^4321*100000000000000^3297 ≤ 35378198810277^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525611939 10000000000 35378198810277 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062300233/5000000000 : ℝ)^4321 ≤ (3132745561337/10000000000000 : ℝ)^3297 := by
    have hnat : (2062300233 : ℕ)^4321*10000000000000^3297 ≤ 3132745561337^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062300233 5000000000 3132745561337 10000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320760231/10000000000 : ℝ), (4525611939/10000000000 : ℝ), (2062300233/5000000000 : ℝ)] ![(33294345557743/100000000000000 : ℝ), (35378198810277/100000000000000 : ℝ), (3132745561337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320760231/10000000000 : ℝ)|^4321 ≤ (33294345557743/100000000000000 : ℝ)^3297
        have hw : |(4320760231/10000000000 : ℝ)|=(4320760231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525611939/10000000000 : ℝ)|^4321 ≤ (35378198810277/100000000000000 : ℝ)^3297
        have hw : |(4525611939/10000000000 : ℝ)|=(4525611939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2062300233/5000000000 : ℝ)|^4321 ≤ (3132745561337/10000000000000 : ℝ)^3297
        have hw : |(2062300233/5000000000 : ℝ)|=(2062300233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41786047/5000000000 : ℝ)*x 0 + (5718387121/10000000000 : ℝ)*x 1 + (3024207893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41786047/5000000000 : ℝ)^4321 ≤ (1477317789/781250000000 : ℝ)^3297 := by
    have hnat : (41786047 : ℕ)^4321*781250000000^3297 ≤ 1477317789^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41786047 5000000000 1477317789 781250000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5718387121/10000000000 : ℝ)^4321 ≤ (24035672120743/50000000000000 : ℝ)^3297 := by
    have hnat : (5718387121 : ℕ)^4321*50000000000000^3297 ≤ 24035672120743^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718387121 10000000000 24035672120743 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3024207893/5000000000 : ℝ)^4321 ≤ (51739559069901/100000000000000 : ℝ)^3297 := by
    have hnat : (3024207893 : ℕ)^4321*100000000000000^3297 ≤ 51739559069901^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3024207893 5000000000 51739559069901 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41786047/5000000000 : ℝ), (5718387121/10000000000 : ℝ), (3024207893/5000000000 : ℝ)] ![(1477317789/781250000000 : ℝ), (24035672120743/50000000000000 : ℝ), (51739559069901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41786047/5000000000 : ℝ)|^4321 ≤ (1477317789/781250000000 : ℝ)^3297
        have hw : |(-41786047/5000000000 : ℝ)|=(41786047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5718387121/10000000000 : ℝ)|^4321 ≤ (24035672120743/50000000000000 : ℝ)^3297
        have hw : |(5718387121/10000000000 : ℝ)|=(5718387121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3024207893/5000000000 : ℝ)|^4321 ≤ (51739559069901/100000000000000 : ℝ)^3297
        have hw : |(3024207893/5000000000 : ℝ)|=(3024207893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020498633/10000000000 : ℝ)*x 0 + (-212517003/500000000 : ℝ)*x 1 + (6977176979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020498633/10000000000 : ℝ)^4321 ≤ (2511505086537/50000000000000 : ℝ)^3297 := by
    have hnat : (1020498633 : ℕ)^4321*50000000000000^3297 ≤ 2511505086537^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020498633 10000000000 2511505086537 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212517003/500000000 : ℝ)^4321 ≤ (32584983472337/100000000000000 : ℝ)^3297 := by
    have hnat : (212517003 : ℕ)^4321*100000000000000^3297 ≤ 32584983472337^3297*500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212517003 500000000 32584983472337 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6977176979/10000000000 : ℝ)^4321 ≤ (62392006340687/100000000000000 : ℝ)^3297 := by
    have hnat : (6977176979 : ℕ)^4321*100000000000000^3297 ≤ 62392006340687^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6977176979 10000000000 62392006340687 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020498633/10000000000 : ℝ), (-212517003/500000000 : ℝ), (6977176979/10000000000 : ℝ)] ![(2511505086537/50000000000000 : ℝ), (32584983472337/100000000000000 : ℝ), (62392006340687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020498633/10000000000 : ℝ)|^4321 ≤ (2511505086537/50000000000000 : ℝ)^3297
        have hw : |(1020498633/10000000000 : ℝ)|=(1020498633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212517003/500000000 : ℝ)|^4321 ≤ (32584983472337/100000000000000 : ℝ)^3297
        have hw : |(-212517003/500000000 : ℝ)|=(212517003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6977176979/10000000000 : ℝ)|^4321 ≤ (62392006340687/100000000000000 : ℝ)^3297
        have hw : |(6977176979/10000000000 : ℝ)|=(6977176979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_10 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (510253723/5000000000 : ℝ)*x 0 + (6977196043/10000000000 : ℝ)*x 1 + (-2125156083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510253723/5000000000 : ℝ)^4321 ≤ (1255766756123/25000000000000 : ℝ)^3297 := by
    have hnat : (510253723 : ℕ)^4321*25000000000000^3297 ≤ 1255766756123^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510253723 5000000000 1255766756123 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6977196043/10000000000 : ℝ)^4321 ≤ (62392229764133/100000000000000 : ℝ)^3297 := by
    have hnat : (6977196043 : ℕ)^4321*100000000000000^3297 ≤ 62392229764133^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6977196043 10000000000 62392229764133 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125156083/5000000000 : ℝ)^4321 ≤ (2036543950433/6250000000000 : ℝ)^3297 := by
    have hnat : (2125156083 : ℕ)^4321*6250000000000^3297 ≤ 2036543950433^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125156083 5000000000 2036543950433 6250000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(510253723/5000000000 : ℝ), (6977196043/10000000000 : ℝ), (-2125156083/5000000000 : ℝ)] ![(1255766756123/25000000000000 : ℝ), (62392229764133/100000000000000 : ℝ), (2036543950433/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(510253723/5000000000 : ℝ)|^4321 ≤ (1255766756123/25000000000000 : ℝ)^3297
        have hw : |(510253723/5000000000 : ℝ)|=(510253723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6977196043/10000000000 : ℝ)|^4321 ≤ (62392229764133/100000000000000 : ℝ)^3297
        have hw : |(6977196043/10000000000 : ℝ)|=(6977196043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125156083/5000000000 : ℝ)|^4321 ≤ (2036543950433/6250000000000 : ℝ)^3297
        have hw : |(-2125156083/5000000000 : ℝ)|=(2125156083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s3_11 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (475637771/5000000000 : ℝ)*x 0 + (5844267163/10000000000 : ℝ)*x 1 + (2762675471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475637771/5000000000 : ℝ)^4321 ≤ (4581241790301/100000000000000 : ℝ)^3297 := by
    have hnat : (475637771 : ℕ)^4321*100000000000000^3297 ≤ 4581241790301^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475637771 5000000000 4581241790301 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5844267163/10000000000 : ℝ)^4321 ≤ (24731464391659/50000000000000 : ℝ)^3297 := by
    have hnat : (5844267163 : ℕ)^4321*50000000000000^3297 ≤ 24731464391659^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5844267163 10000000000 24731464391659 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762675471/5000000000 : ℝ)^4321 ≤ (1436119669359/3125000000000 : ℝ)^3297 := by
    have hnat : (2762675471 : ℕ)^4321*3125000000000^3297 ≤ 1436119669359^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762675471 5000000000 1436119669359 3125000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(475637771/5000000000 : ℝ), (5844267163/10000000000 : ℝ), (2762675471/5000000000 : ℝ)] ![(4581241790301/100000000000000 : ℝ), (24731464391659/50000000000000 : ℝ), (1436119669359/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(475637771/5000000000 : ℝ)|^4321 ≤ (4581241790301/100000000000000 : ℝ)^3297
        have hw : |(475637771/5000000000 : ℝ)|=(475637771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5844267163/10000000000 : ℝ)|^4321 ≤ (24731464391659/50000000000000 : ℝ)^3297
        have hw : |(5844267163/10000000000 : ℝ)|=(5844267163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762675471/5000000000 : ℝ)|^4321 ≤ (1436119669359/3125000000000 : ℝ)^3297
        have hw : |(2762675471/5000000000 : ℝ)|=(2762675471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1361_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1367/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (937/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9973/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9973/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9973/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9973/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9973/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9973/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9973/100000 : ℝ) ^ (135/32 : ℝ) ≤ (5974429271388751/100000000000000000000 : ℝ) := by
    have hpowers : (9973/100000 : ℝ)^135 ≤ (5974429271388751/100000000000000000000 : ℝ)^32 := by
      have hnat : (9973 : ℕ)^135*100000000000000000000^32 ≤ 5974429271388751^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9973 100000 5974429271388751 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9973/100000 : ℝ)) (X := (5974429271388751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hpowhi : (16031/100000 : ℝ) ^ (135/32 : ℝ) ≤ (44251458648747097/100000000000000000000 : ℝ) := by
    have hpowers : (16031/100000 : ℝ)^135 ≤ (44251458648747097/100000000000000000000 : ℝ)^32 := by
      have hnat : (16031 : ℕ)^135*100000000000000000000^32 ≤ 44251458648747097^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16031 100000 44251458648747097 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16031/100000 : ℝ)) (X := (44251458648747097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005974429271388751/50000000000000000000 : ℝ) ≤ (10000283219292919/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (50005974429271388751/50000000000000000000 : ℝ)^32 ≤ (10000283219292919/10000000000000000 : ℝ)^135 := by
      have hnat : (50005974429271388751 : ℕ)^32*10000000000000000^135 ≤ 10000283219292919^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005974429271388751 50000000000000000000 10000283219292919 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283219292919/10000000000000000 : ℝ)) (X := (50005974429271388751/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506278235990016981/12500000000000000000 : ℝ) ≤ (2500297577880627/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (12506278235990016981/12500000000000000000 : ℝ)^32 ≤ (2500297577880627/2500000000000000 : ℝ)^135 := by
      have hnat : (12506278235990016981 : ℕ)^32*2500000000000000^135 ≤ 2500297577880627^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506278235990016981 12500000000000000000 2500297577880627 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500297577880627/2500000000000000 : ℝ)) (X := (12506278235990016981/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044251458648747097/50000000000000000000 : ℝ) ≤ (10002097403752097/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (50044251458648747097/50000000000000000000 : ℝ)^32 ≤ (10002097403752097/10000000000000000 : ℝ)^135 := by
      have hnat : (50044251458648747097 : ℕ)^32*10000000000000000^135 ≤ 10002097403752097^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044251458648747097 50000000000000000000 10002097403752097 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002097403752097/10000000000000000 : ℝ)) (X := (50044251458648747097/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5974429271388751/100000000000000000000 : ℝ) ≤ ((1164685055401252329/1165000000000000000 : ℝ)+2*(69776325353/46600000000000 : ℝ)*(9973/100000 : ℝ))^(135/32 : ℝ) := by
    rw [show (1164685055401252329/1165000000000000000 : ℝ)+2*(69776325353/46600000000000 : ℝ)*(9973/100000 : ℝ)=(10000283219292919/10000000000000000 : ℝ) by norm_num, show 1+2*(5974429271388751/100000000000000000000 : ℝ)=(50005974429271388751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44251458648747097/100000000000000000000 : ℝ)+(5974429271388751/100000000000000000000 : ℝ) ≤ ((1164685055401252329/1165000000000000000 : ℝ)+(69776325353/46600000000000 : ℝ)*((16031/100000 : ℝ)+(9973/100000 : ℝ)))^(135/32 : ℝ) := by
    rw [show (1164685055401252329/1165000000000000000 : ℝ)+(69776325353/46600000000000 : ℝ)*((16031/100000 : ℝ)+(9973/100000 : ℝ))=(2500297577880627/2500000000000000 : ℝ) by norm_num, show 1+(44251458648747097/100000000000000000000 : ℝ)+(5974429271388751/100000000000000000000 : ℝ)=(12506278235990016981/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44251458648747097/100000000000000000000 : ℝ) ≤ ((1164685055401252329/1165000000000000000 : ℝ)+2*(69776325353/46600000000000 : ℝ)*(16031/100000 : ℝ))^(135/32 : ℝ) := by
    rw [show (1164685055401252329/1165000000000000000 : ℝ)+2*(69776325353/46600000000000 : ℝ)*(16031/100000 : ℝ)=(10002097403752097/10000000000000000 : ℝ) by norm_num, show 1+2*(44251458648747097/100000000000000000000 : ℝ)=(50044251458648747097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1164685055401252329/1165000000000000000 : ℝ)*(X 1 0+X 2 0)+(69776325353/46600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (9973/100000 : ℝ)) (hi := (16031/100000 : ℝ)) (c := (1164685055401252329/1165000000000000000 : ℝ)) (alpha := (69776325353/46600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1164685055401252329/1165000000000000000 : ℝ)*(X 0 1+X 2 1)+(69776325353/46600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (9973/100000 : ℝ)) (hi := (16031/100000 : ℝ)) (c := (1164685055401252329/1165000000000000000 : ℝ)) (alpha := (69776325353/46600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1164685055401252329/1165000000000000000 : ℝ)*(X 0 2+X 1 2)+(69776325353/46600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (9973/100000 : ℝ)) (hi := (16031/100000 : ℝ)) (c := (1164685055401252329/1165000000000000000 : ℝ)) (alpha := (69776325353/46600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2026094339/10000000000 : ℝ)*X 0 0+(1084961357/2000000000 : ℝ)*X 0 1+(523312887/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214080273/400000000 : ℝ)*X 1 0+(-2124010739/10000000000 : ℝ)*X 1 1+(654141107/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070401433/2000000000 : ℝ)*X 2 0+(2616564217/5000000000 : ℝ)*X 2 1+(-531002711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320722199/10000000000 : ℝ)*X 0 0+(25768269/62500000 : ℝ)*X 0 1+(4527279007/10000000000 : ℝ)*X 0 2+(4320722199/10000000000 : ℝ)*X 1 0+(25768269/62500000 : ℝ)*X 1 1+(4527279007/10000000000 : ℝ)*X 1 2+(4320722199/10000000000 : ℝ)*X 2 0+(25768269/62500000 : ℝ)*X 2 1+(4527279007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-101305671/500000000 : ℝ)*X 0 0+(327119927/625000000 : ℝ)*X 0 1+(542401151/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651263827/5000000000 : ℝ)*X 1 0+(-1933127851/10000000000 : ℝ)*X 1 1+(5424012039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060505759/2000000000 : ℝ)*X 2 0+(678001407/1250000000 : ℝ)*X 2 1+(-193312737/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320760231/10000000000 : ℝ)*X 0 0+(4525611939/10000000000 : ℝ)*X 0 1+(2062300233/5000000000 : ℝ)*X 0 2+(4320760231/10000000000 : ℝ)*X 1 0+(4525611939/10000000000 : ℝ)*X 1 1+(2062300233/5000000000 : ℝ)*X 1 2+(4320760231/10000000000 : ℝ)*X 2 0+(4525611939/10000000000 : ℝ)*X 2 1+(2062300233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-41786047/5000000000 : ℝ)*X 0 0+(5718387121/10000000000 : ℝ)*X 0 1+(3024207893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1020498633/10000000000 : ℝ)*X 1 0+(-212517003/500000000 : ℝ)*X 1 1+(6977176979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((510253723/5000000000 : ℝ)*X 2 0+(6977196043/10000000000 : ℝ)*X 2 1+(-2125156083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((475637771/5000000000 : ℝ)*X 0 0+(5844267163/10000000000 : ℝ)*X 0 1+(2762675471/5000000000 : ℝ)*X 0 2+(475637771/5000000000 : ℝ)*X 1 0+(5844267163/10000000000 : ℝ)*X 1 1+(2762675471/5000000000 : ℝ)*X 1 2+(475637771/5000000000 : ℝ)*X 2 0+(5844267163/10000000000 : ℝ)*X 2 1+(2762675471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225104351868288302862564273/58250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52064911/10000000000000 : ℝ)*(lower2) + (2072323/1000000000000 : ℝ)*(lower4) + (3845074108049007/100000000000000 : ℝ)*(major0) + (3845074108049007/100000000000000 : ℝ)*(major1) + (3845074108049007/100000000000000 : ℝ)*(major2) + (652134674038227/12500000000000 : ℝ)*(sp0) + (2608538869284267/50000000000000 : ℝ)*(sp1) + (260853606062061/5000000000000 : ℝ)*(sp2) + (2473067415719151/100000000000000 : ℝ)*(sp3) + (1499981427/25000000000000 : ℝ)*(sp6) + (1997679801/100000000000000 : ℝ)*(sp7) + (91107639/12500000000000 : ℝ)*(sp8) + (191299197/50000000000000 : ℝ)*(sp9) + (138179261/25000000000000 : ℝ)*(sp11) + (2473069966115997/100000000000000 : ℝ)*(f.failure) + (326067382572933/6250000000000 : ℝ)*(f.sum) + (2126486366391/2330000000000000000000000000 : ℝ)*base65 + (2194824858627162303/116500000000000000000000000000000 : ℝ)*base67 + (206820131337162303/116500000000000000000000000000000 : ℝ)*base69 + (544008742546662303/116500000000000000000000000000000 : ℝ)*base71 + (10034789906421/2330000000000000000000000000 : ℝ)*base73 + (1485131890050162303/116500000000000000000000000000000 : ℝ)*base75 + (1138058178814662303/116500000000000000000000000000000 : ℝ)*base77 + (1516757739863162303/116500000000000000000000000000000 : ℝ)*base79 + (7101252229241/2330000000000000000000000000 : ℝ)*base81 + (26765319/10000000000000000000000 : ℝ)*base90 + (26765319/10000000000000000000000 : ℝ)*base92 + (26765319/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7770120949331238455633499/2912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209810707/100000000000000 : ℝ)*(lower2) + (387715046253423/10000000000000 : ℝ)*(major0) + (387715046253423/10000000000000 : ℝ)*(major1) + (387715046253423/10000000000000 : ℝ)*(major2) + (9105182387/100000000000000 : ℝ)*(sp1) + (947516801/25000000000000 : ℝ)*(sp2) + (151160109/12500000000000 : ℝ)*(sp3) + (1315149591763247/25000000000000 : ℝ)*(sp4) + (5260590935195517/100000000000000 : ℝ)*(sp5) + (2630297699976821/50000000000000 : ℝ)*(sp6) + (1246849300289421/50000000000000 : ℝ)*(sp7) + (334664983/20000000000000 : ℝ)*(sp8) + (425178529/50000000000000 : ℝ)*(sp10) + (98590241/10000000000000 : ℝ)*(sp11) + (19949606366097/800000000000 : ℝ)*(f.failure) + (5260600040377903/100000000000000 : ℝ)*(f.sum) + (99429083079/233000000000000000000000000 : ℝ)*base65 + (86319168415597167/11650000000000000000000000000000 : ℝ)*base67 + (32827882512047167/11650000000000000000000000000000 : ℝ)*base69 + (7146994055002833/11650000000000000000000000000000 : ℝ)*base72 + (80847698583/46600000000000000000000000 : ℝ)*base73 + (45707093059797167/11650000000000000000000000000000 : ℝ)*base75 + (335663884378747167/11650000000000000000000000000000 : ℝ)*base77 + (52479359231447167/11650000000000000000000000000000 : ℝ)*base79 + (1784925436303/233000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (261981/80000000000000000000 : ℝ)*base89 + (261981/80000000000000000000 : ℝ)*base91 + (261981/80000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1361_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (937/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1361_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1361_s4_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013705133/5000000000 : ℝ)*x 0 + (270698041/500000000 : ℝ)*x 1 + (2621555101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013705133/5000000000 : ℝ)^4321 ≤ (3087648511873/25000000000000 : ℝ)^3297 := by
    have hnat : (1013705133 : ℕ)^4321*25000000000000^3297 ≤ 3087648511873^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013705133 5000000000 3087648511873 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270698041/500000000 : ℝ)^4321 ≤ (44745441446057/100000000000000 : ℝ)^3297 := by
    have hnat : (270698041 : ℕ)^4321*100000000000000^3297 ≤ 44745441446057^3297*500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270698041 500000000 44745441446057 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621555101/5000000000 : ℝ)^4321 ≤ (42903964487613/100000000000000 : ℝ)^3297 := by
    have hnat : (2621555101 : ℕ)^4321*100000000000000^3297 ≤ 42903964487613^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621555101 5000000000 42903964487613 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013705133/5000000000 : ℝ), (270698041/500000000 : ℝ), (2621555101/5000000000 : ℝ)] ![(3087648511873/25000000000000 : ℝ), (44745441446057/100000000000000 : ℝ), (42903964487613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013705133/5000000000 : ℝ)|^4321 ≤ (3087648511873/25000000000000 : ℝ)^3297
        have hw : |(-1013705133/5000000000 : ℝ)|=(1013705133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270698041/500000000 : ℝ)|^4321 ≤ (44745441446057/100000000000000 : ℝ)^3297
        have hw : |(270698041/500000000 : ℝ)|=(270698041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621555101/5000000000 : ℝ)|^4321 ≤ (42903964487613/100000000000000 : ℝ)^3297
        have hw : |(2621555101/5000000000 : ℝ)|=(2621555101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133730859/250000000 : ℝ)*x 0 + (-1057243767/5000000000 : ℝ)*x 1 + (327694351/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133730859/250000000 : ℝ)^4321 ≤ (44045645257251/100000000000000 : ℝ)^3297 := by
    have hnat : (133730859 : ℕ)^4321*100000000000000^3297 ≤ 44045645257251^3297*250000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133730859 250000000 44045645257251 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057243767/5000000000 : ℝ)^4321 ≤ (13050396516709/100000000000000 : ℝ)^3297 := by
    have hnat : (1057243767 : ℕ)^4321*100000000000000^3297 ≤ 13050396516709^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057243767 5000000000 13050396516709 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327694351/625000000 : ℝ)^4321 ≤ (1340748693847/3125000000000 : ℝ)^3297 := by
    have hnat : (327694351 : ℕ)^4321*3125000000000^3297 ≤ 1340748693847^3297*625000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327694351 625000000 1340748693847 3125000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133730859/250000000 : ℝ), (-1057243767/5000000000 : ℝ), (327694351/625000000 : ℝ)] ![(44045645257251/100000000000000 : ℝ), (13050396516709/100000000000000 : ℝ), (1340748693847/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133730859/250000000 : ℝ)|^4321 ≤ (44045645257251/100000000000000 : ℝ)^3297
        have hw : |(133730859/250000000 : ℝ)|=(133730859/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057243767/5000000000 : ℝ)|^4321 ≤ (13050396516709/100000000000000 : ℝ)^3297
        have hw : |(-1057243767/5000000000 : ℝ)|=(1057243767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327694351/625000000 : ℝ)|^4321 ≤ (1340748693847/3125000000000 : ℝ)^3297
        have hw : |(327694351/625000000 : ℝ)|=(327694351/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674617399/5000000000 : ℝ)*x 0 + (1048621971/2000000000 : ℝ)*x 1 + (-422897327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674617399/5000000000 : ℝ)^4321 ≤ (344106640499/781250000000 : ℝ)^3297 := by
    have hnat : (2674617399 : ℕ)^4321*781250000000^3297 ≤ 344106640499^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674617399 5000000000 344106640499 781250000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048621971/2000000000 : ℝ)^4321 ≤ (268149754789/625000000000 : ℝ)^3297 := by
    have hnat : (1048621971 : ℕ)^4321*625000000000^3297 ≤ 268149754789^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048621971 2000000000 268149754789 625000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422897327/2000000000 : ℝ)^4321 ≤ (13050389244881/100000000000000 : ℝ)^3297 := by
    have hnat : (422897327 : ℕ)^4321*100000000000000^3297 ≤ 13050389244881^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422897327 2000000000 13050389244881 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674617399/5000000000 : ℝ), (1048621971/2000000000 : ℝ), (-422897327/2000000000 : ℝ)] ![(344106640499/781250000000 : ℝ), (268149754789/625000000000 : ℝ), (13050389244881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674617399/5000000000 : ℝ)|^4321 ≤ (344106640499/781250000000 : ℝ)^3297
        have hw : |(2674617399/5000000000 : ℝ)|=(2674617399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048621971/2000000000 : ℝ)|^4321 ≤ (268149754789/625000000000 : ℝ)^3297
        have hw : |(1048621971/2000000000 : ℝ)|=(1048621971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422897327/2000000000 : ℝ)|^4321 ≤ (13050389244881/100000000000000 : ℝ)^3297
        have hw : |(-422897327/2000000000 : ℝ)|=(422897327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135047497/312500000 : ℝ)*x 0 + (4144794777/10000000000 : ℝ)*x 1 + (4505213231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135047497/312500000 : ℝ)^4321 ≤ (1332080706259/4000000000000 : ℝ)^3297 := by
    have hnat : (135047497 : ℕ)^4321*4000000000000^3297 ≤ 1332080706259^3297*312500000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135047497 312500000 1332080706259 4000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144794777/10000000000 : ℝ)^4321 ≤ (31528627507221/100000000000000 : ℝ)^3297 := by
    have hnat : (4144794777 : ℕ)^4321*100000000000000^3297 ≤ 31528627507221^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144794777 10000000000 31528627507221 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505213231/10000000000 : ℝ)^4321 ≤ (35169354824067/100000000000000 : ℝ)^3297 := by
    have hnat : (4505213231 : ℕ)^4321*100000000000000^3297 ≤ 35169354824067^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505213231 10000000000 35169354824067 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135047497/312500000 : ℝ), (4144794777/10000000000 : ℝ), (4505213231/10000000000 : ℝ)] ![(1332080706259/4000000000000 : ℝ), (31528627507221/100000000000000 : ℝ), (35169354824067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135047497/312500000 : ℝ)|^4321 ≤ (1332080706259/4000000000000 : ℝ)^3297
        have hw : |(135047497/312500000 : ℝ)|=(135047497/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144794777/10000000000 : ℝ)|^4321 ≤ (31528627507221/100000000000000 : ℝ)^3297
        have hw : |(4144794777/10000000000 : ℝ)|=(4144794777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505213231/10000000000 : ℝ)|^4321 ≤ (35169354824067/100000000000000 : ℝ)^3297
        have hw : |(4505213231/10000000000 : ℝ)|=(4505213231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013711707/5000000000 : ℝ)*x 0 + (524373831/1000000000 : ℝ)*x 1 + (5413329223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013711707/5000000000 : ℝ)^4321 ≤ (6175349509527/50000000000000 : ℝ)^3297 := by
    have hnat : (1013711707 : ℕ)^4321*50000000000000^3297 ≤ 6175349509527^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013711707 5000000000 6175349509527 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524373831/1000000000 : ℝ)^4321 ≤ (858214014121/2000000000000 : ℝ)^3297 := by
    have hnat : (524373831 : ℕ)^4321*2000000000000^3297 ≤ 858214014121^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524373831 1000000000 858214014121 2000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413329223/10000000000 : ℝ)^4321 ≤ (11184650065803/25000000000000 : ℝ)^3297 := by
    have hnat : (5413329223 : ℕ)^4321*25000000000000^3297 ≤ 11184650065803^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413329223 10000000000 11184650065803 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013711707/5000000000 : ℝ), (524373831/1000000000 : ℝ), (5413329223/10000000000 : ℝ)] ![(6175349509527/50000000000000 : ℝ), (858214014121/2000000000000 : ℝ), (11184650065803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013711707/5000000000 : ℝ)|^4321 ≤ (6175349509527/50000000000000 : ℝ)^3297
        have hw : |(-1013711707/5000000000 : ℝ)|=(1013711707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524373831/1000000000 : ℝ)|^4321 ≤ (858214014121/2000000000000 : ℝ)^3297
        have hw : |(524373831/1000000000 : ℝ)|=(524373831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413329223/10000000000 : ℝ)|^4321 ≤ (11184650065803/25000000000000 : ℝ)^3297
        have hw : |(5413329223/10000000000 : ℝ)|=(5413329223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265256641/500000000 : ℝ)*x 0 + (-486066789/2500000000 : ℝ)*x 1 + (2706664563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265256641/500000000 : ℝ)^4321 ≤ (272314622513/625000000000 : ℝ)^3297 := by
    have hnat : (265256641 : ℕ)^4321*625000000000^3297 ≤ 272314622513^3297*500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265256641 500000000 272314622513 625000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486066789/2500000000 : ℝ)^4321 ≤ (1461382645603/12500000000000 : ℝ)^3297 := by
    have hnat : (486066789 : ℕ)^4321*12500000000000^3297 ≤ 1461382645603^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486066789 2500000000 1461382645603 12500000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706664563/5000000000 : ℝ)^4321 ≤ (4473859921257/10000000000000 : ℝ)^3297 := by
    have hnat : (2706664563 : ℕ)^4321*10000000000000^3297 ≤ 4473859921257^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706664563 5000000000 4473859921257 10000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265256641/500000000 : ℝ), (-486066789/2500000000 : ℝ), (2706664563/5000000000 : ℝ)] ![(272314622513/625000000000 : ℝ), (1461382645603/12500000000000 : ℝ), (4473859921257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265256641/500000000 : ℝ)|^4321 ≤ (272314622513/625000000000 : ℝ)^3297
        have hw : |(265256641/500000000 : ℝ)|=(265256641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486066789/2500000000 : ℝ)|^4321 ≤ (1461382645603/12500000000000 : ℝ)^3297
        have hw : |(-486066789/2500000000 : ℝ)|=(486066789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706664563/5000000000 : ℝ)|^4321 ≤ (4473859921257/10000000000000 : ℝ)^3297
        have hw : |(2706664563/5000000000 : ℝ)|=(2706664563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530513263/1000000000 : ℝ)*x 0 + (1353332337/2500000000 : ℝ)*x 1 + (-1944267111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530513263/1000000000 : ℝ)^4321 ≤ (5446292194623/12500000000000 : ℝ)^3297 := by
    have hnat : (530513263 : ℕ)^4321*12500000000000^3297 ≤ 5446292194623^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530513263 1000000000 5446292194623 12500000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353332337/2500000000 : ℝ)^4321 ≤ (44738601617133/100000000000000 : ℝ)^3297 := by
    have hnat : (1353332337 : ℕ)^4321*100000000000000^3297 ≤ 44738601617133^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353332337 2500000000 44738601617133 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944267111/10000000000 : ℝ)^4321 ≤ (5845530405097/50000000000000 : ℝ)^3297 := by
    have hnat : (1944267111 : ℕ)^4321*50000000000000^3297 ≤ 5845530405097^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944267111 10000000000 5845530405097 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530513263/1000000000 : ℝ), (1353332337/2500000000 : ℝ), (-1944267111/10000000000 : ℝ)] ![(5446292194623/12500000000000 : ℝ), (44738601617133/100000000000000 : ℝ), (5845530405097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530513263/1000000000 : ℝ)|^4321 ≤ (5446292194623/12500000000000 : ℝ)^3297
        have hw : |(530513263/1000000000 : ℝ)|=(530513263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353332337/2500000000 : ℝ)|^4321 ≤ (44738601617133/100000000000000 : ℝ)^3297
        have hw : |(1353332337/2500000000 : ℝ)|=(1353332337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944267111/10000000000 : ℝ)|^4321 ≤ (5845530405097/50000000000000 : ℝ)^3297
        have hw : |(-1944267111/10000000000 : ℝ)|=(1944267111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s4_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160774187/5000000000 : ℝ)*x 0 + (4503887553/10000000000 : ℝ)*x 1 + (829225253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160774187/5000000000 : ℝ)^4321 ≤ (33302305189187/100000000000000 : ℝ)^3297 := by
    have hnat : (2160774187 : ℕ)^4321*100000000000000^3297 ≤ 33302305189187^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160774187 5000000000 33302305189187 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503887553/10000000000 : ℝ)^4321 ≤ (1406231701931/4000000000000 : ℝ)^3297 := by
    have hnat : (4503887553 : ℕ)^4321*4000000000000^3297 ≤ 1406231701931^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503887553 10000000000 1406231701931 4000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829225253/2000000000 : ℝ)^4321 ≤ (15770951127419/50000000000000 : ℝ)^3297 := by
    have hnat : (829225253 : ℕ)^4321*50000000000000^3297 ≤ 15770951127419^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829225253 2000000000 15770951127419 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160774187/5000000000 : ℝ), (4503887553/10000000000 : ℝ), (829225253/2000000000 : ℝ)] ![(33302305189187/100000000000000 : ℝ), (1406231701931/4000000000000 : ℝ), (15770951127419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160774187/5000000000 : ℝ)|^4321 ≤ (33302305189187/100000000000000 : ℝ)^3297
        have hw : |(2160774187/5000000000 : ℝ)|=(2160774187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503887553/10000000000 : ℝ)|^4321 ≤ (1406231701931/4000000000000 : ℝ)^3297
        have hw : |(4503887553/10000000000 : ℝ)|=(4503887553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829225253/2000000000 : ℝ)|^4321 ≤ (15770951127419/50000000000000 : ℝ)^3297
        have hw : |(829225253/2000000000 : ℝ)|=(829225253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1361_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (937/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (937/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1367/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (937/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1367/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (937/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1367/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (937/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1367/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (937/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1367/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (937/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1367/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1367/12500 : ℝ) ^ (135/32 : ℝ) ≤ (8814228469317541/100000000000000000000 : ℝ) := by
    have hpowers : (1367/12500 : ℝ)^135 ≤ (8814228469317541/100000000000000000000 : ℝ)^32 := by
      have hnat : (1367 : ℕ)^135*100000000000000000000^32 ≤ 8814228469317541^32*12500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1367 12500 8814228469317541 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1367/12500 : ℝ)) (X := (8814228469317541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hpowhi : (937/6250 : ℝ) ^ (135/32 : ℝ) ≤ (16677370622427699/50000000000000000000 : ℝ) := by
    have hpowers : (937/6250 : ℝ)^135 ≤ (16677370622427699/50000000000000000000 : ℝ)^32 := by
      have hnat : (937 : ℕ)^135*50000000000000000000^32 ≤ 16677370622427699^32*6250^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        937 6250 16677370622427699 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (937/6250 : ℝ)) (X := (16677370622427699/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008814228469317541/50000000000000000000 : ℝ) ≤ (2000083566324433/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (50008814228469317541/50000000000000000000 : ℝ)^32 ≤ (2000083566324433/2000000000000000 : ℝ)^135 := by
      have hnat : (50008814228469317541 : ℕ)^32*2000000000000000^135 ≤ 2000083566324433^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008814228469317541 50000000000000000000 2000083566324433 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000083566324433/2000000000000000 : ℝ)) (X := (50008814228469317541/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042168969714172939/100000000000000000000 : ℝ) ≤ (10000999400007279/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (100042168969714172939/100000000000000000000 : ℝ)^32 ≤ (10000999400007279/10000000000000000 : ℝ)^135 := by
      have hnat : (100042168969714172939 : ℕ)^32*10000000000000000^135 ≤ 10000999400007279^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042168969714172939 100000000000000000000 10000999400007279 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000999400007279/10000000000000000 : ℝ)) (X := (100042168969714172939/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016677370622427699/25000000000000000000 : ℝ) ≤ (10001580968392393/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (25016677370622427699/25000000000000000000 : ℝ)^32 ≤ (10001580968392393/10000000000000000 : ℝ)^135 := by
      have hnat : (25016677370622427699 : ℕ)^32*10000000000000000^135 ≤ 10001580968392393^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016677370622427699 25000000000000000000 10001580968392393 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001580968392393/10000000000000000 : ℝ)) (X := (25016677370622427699/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8814228469317541/100000000000000000000 : ℝ) ≤ ((5068621832667535979/5070000000000000000 : ℝ)+2*(290784192557/202800000000000 : ℝ)*(1367/12500 : ℝ))^(135/32 : ℝ) := by
    rw [show (5068621832667535979/5070000000000000000 : ℝ)+2*(290784192557/202800000000000 : ℝ)*(1367/12500 : ℝ)=(2000083566324433/2000000000000000 : ℝ) by norm_num, show 1+2*(8814228469317541/100000000000000000000 : ℝ)=(50008814228469317541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16677370622427699/50000000000000000000 : ℝ)+(8814228469317541/100000000000000000000 : ℝ) ≤ ((5068621832667535979/5070000000000000000 : ℝ)+(290784192557/202800000000000 : ℝ)*((937/6250 : ℝ)+(1367/12500 : ℝ)))^(135/32 : ℝ) := by
    rw [show (5068621832667535979/5070000000000000000 : ℝ)+(290784192557/202800000000000 : ℝ)*((937/6250 : ℝ)+(1367/12500 : ℝ))=(10000999400007279/10000000000000000 : ℝ) by norm_num, show 1+(16677370622427699/50000000000000000000 : ℝ)+(8814228469317541/100000000000000000000 : ℝ)=(100042168969714172939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16677370622427699/50000000000000000000 : ℝ) ≤ ((5068621832667535979/5070000000000000000 : ℝ)+2*(290784192557/202800000000000 : ℝ)*(937/6250 : ℝ))^(135/32 : ℝ) := by
    rw [show (5068621832667535979/5070000000000000000 : ℝ)+2*(290784192557/202800000000000 : ℝ)*(937/6250 : ℝ)=(10001580968392393/10000000000000000 : ℝ) by norm_num, show 1+2*(16677370622427699/50000000000000000000 : ℝ)=(25016677370622427699/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5068621832667535979/5070000000000000000 : ℝ)*(X 1 0+X 2 0)+(290784192557/202800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (937/6250 : ℝ)) (c := (5068621832667535979/5070000000000000000 : ℝ)) (alpha := (290784192557/202800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5068621832667535979/5070000000000000000 : ℝ)*(X 0 1+X 2 1)+(290784192557/202800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (937/6250 : ℝ)) (c := (5068621832667535979/5070000000000000000 : ℝ)) (alpha := (290784192557/202800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5068621832667535979/5070000000000000000 : ℝ)*(X 0 2+X 1 2)+(290784192557/202800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (1367/12500 : ℝ)) (hi := (937/6250 : ℝ)) (c := (5068621832667535979/5070000000000000000 : ℝ)) (alpha := (290784192557/202800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1013705133/5000000000 : ℝ)*X 0 0+(270698041/500000000 : ℝ)*X 0 1+(2621555101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133730859/250000000 : ℝ)*X 1 0+(-1057243767/5000000000 : ℝ)*X 1 1+(327694351/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674617399/5000000000 : ℝ)*X 2 0+(1048621971/2000000000 : ℝ)*X 2 1+(-422897327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135047497/312500000 : ℝ)*X 0 0+(4144794777/10000000000 : ℝ)*X 0 1+(4505213231/10000000000 : ℝ)*X 0 2+(135047497/312500000 : ℝ)*X 1 0+(4144794777/10000000000 : ℝ)*X 1 1+(4505213231/10000000000 : ℝ)*X 1 2+(135047497/312500000 : ℝ)*X 2 0+(4144794777/10000000000 : ℝ)*X 2 1+(4505213231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1013711707/5000000000 : ℝ)*X 0 0+(524373831/1000000000 : ℝ)*X 0 1+(5413329223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265256641/500000000 : ℝ)*X 1 0+(-486066789/2500000000 : ℝ)*X 1 1+(2706664563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530513263/1000000000 : ℝ)*X 2 0+(1353332337/2500000000 : ℝ)*X 2 1+(-1944267111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160774187/5000000000 : ℝ)*X 0 0+(4503887553/10000000000 : ℝ)*X 0 1+(829225253/2000000000 : ℝ)*X 0 2+(2160774187/5000000000 : ℝ)*X 1 0+(4503887553/10000000000 : ℝ)*X 1 1+(829225253/2000000000 : ℝ)*X 1 2+(2160774187/5000000000 : ℝ)*X 2 0+(4503887553/10000000000 : ℝ)*X 2 1+(829225253/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19778015593438286338501/3380000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55956283/25000000000000 : ℝ)*(base8) + (394553/1250000000000 : ℝ)*(base21) + (48336019/50000000000000 : ℝ)*(base29) + (26429301/25000000000000 : ℝ)*(lower3) + (175331771/50000000000000 : ℝ)*(upper4) + (4313807505412747/100000000000000 : ℝ)*(major0) + (862761520416957/20000000000000 : ℝ)*(major1) + (862761520416957/20000000000000 : ℝ)*(major2) + (365816084766009/6250000000000 : ℝ)*(sp0) + (5853047468948411/100000000000000 : ℝ)*(sp1) + (2926532745529479/50000000000000 : ℝ)*(sp2) + (1387274694912431/50000000000000 : ℝ)*(sp3) + (8039213959/100000000000000 : ℝ)*(sp4) + (9026837393/50000000000000 : ℝ)*(sp5) + (1387274694912431/50000000000000 : ℝ)*(f.failure) + (1170613123859047/20000000000000 : ℝ)*(f.sum) + (384891456577/135200000000000000000000000 : ℝ)*base66 + (95480519732059699/33800000000000000000000000000000 : ℝ)*base68 + (229930301070540301/33800000000000000000000000000000 : ℝ)*base69 + (2212696762402849313/507000000000000000000000000000000 : ℝ)*base71 + (7866626539451/5070000000000000000000000000 : ℝ)*base73 + (346203763231990903/101400000000000000000000000000000 : ℝ)*base75 + (4885071033625150687/507000000000000000000000000000000 : ℝ)*base78 + (458525956510009097/101400000000000000000000000000000 : ℝ)*base80 + (7468560011891/5070000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (48103837/5000000000000000000000 : ℝ)*base90 + (48103837/5000000000000000000000 : ℝ)*base92 + (48103837/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7866585864825165182283/845000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157433397/10000000000000 : ℝ)*(base19) + (1480549419/100000000000000 : ℝ)*(base23) + (38028399/50000000000000 : ℝ)*(upper3) + (27317007/50000000000000 : ℝ)*(lower4) + (112769009/100000000000000 : ℝ)*(upper5) + (1086462455368613/25000000000000 : ℝ)*(major0) + (1086462455368613/25000000000000 : ℝ)*(major1) + (1086462455368613/25000000000000 : ℝ)*(major2) + (34593092881/100000000000000 : ℝ)*(sp1) + (36326367117/100000000000000 : ℝ)*(sp2) + (737067633515887/12500000000000 : ℝ)*(sp4) + (1179300980140049/20000000000000 : ℝ)*(sp5) + (18426572691283/312500000000 : ℝ)*(sp6) + (174697391531427/6250000000000 : ℝ)*(sp7) + (174697391531427/6250000000000 : ℝ)*(f.failure) + (737067633515887/12500000000000 : ℝ)*(f.sum) + (17413059476399/2535000000000000000000000000 : ℝ)*base66 + (747218056027147873/126750000000000000000000000000000 : ℝ)*base68 + (199108720666852127/126750000000000000000000000000000 : ℝ)*base69 + (1448833728928147873/126750000000000000000000000000000 : ℝ)*base72 + (11468438841329/2535000000000000000000000000 : ℝ)*base74 + (2360050057890352127/126750000000000000000000000000000 : ℝ)*base75 + (674109603863647873/126750000000000000000000000000000 : ℝ)*base78 + (684815465576602127/126750000000000000000000000000000 : ℝ)*base79 + (3735951932467/1267500000000000000000000000 : ℝ)*base82 + (4472071/625000000000000000000 : ℝ)*base89 + (4472071/625000000000000000000 : ℝ)*base91 + (4472071/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1361_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (937/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1367/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1361_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1361_s5_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2027629049/10000000000 : ℝ)*x 0 + (5412055297/10000000000 : ℝ)*x 1 + (1311217931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027629049/10000000000 : ℝ)^4321 ≤ (1544042600503/12500000000000 : ℝ)^3297 := by
    have hnat : (2027629049 : ℕ)^4321*12500000000000^3297 ≤ 1544042600503^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027629049 10000000000 1544042600503 12500000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412055297/10000000000 : ℝ)^4321 ≤ (44724802407479/100000000000000 : ℝ)^3297 := by
    have hnat : (5412055297 : ℕ)^4321*100000000000000^3297 ≤ 44724802407479^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412055297 10000000000 44724802407479 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311217931/2500000000 : ℝ)^4321 ≤ (21461428386241/50000000000000 : ℝ)^3297 := by
    have hnat : (1311217931 : ℕ)^4321*50000000000000^3297 ≤ 21461428386241^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311217931 2500000000 21461428386241 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2027629049/10000000000 : ℝ), (5412055297/10000000000 : ℝ), (1311217931/2500000000 : ℝ)] ![(1544042600503/12500000000000 : ℝ), (44724802407479/100000000000000 : ℝ), (21461428386241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2027629049/10000000000 : ℝ)|^4321 ≤ (1544042600503/12500000000000 : ℝ)^3297
        have hw : |(-2027629049/10000000000 : ℝ)|=(2027629049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412055297/10000000000 : ℝ)|^4321 ≤ (44724802407479/100000000000000 : ℝ)^3297
        have hw : |(5412055297/10000000000 : ℝ)|=(5412055297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311217931/2500000000 : ℝ)|^4321 ≤ (21461428386241/50000000000000 : ℝ)^3297
        have hw : |(1311217931/2500000000 : ℝ)|=(1311217931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337186733/2500000000 : ℝ)*x 0 + (-2112801159/10000000000 : ℝ)*x 1 + (1048974353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337186733/2500000000 : ℝ)^4321 ≤ (22020192657367/50000000000000 : ℝ)^3297 := by
    have hnat : (1337186733 : ℕ)^4321*50000000000000^3297 ≤ 22020192657367^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337186733 2500000000 22020192657367 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112801159/10000000000 : ℝ)^4321 ≤ (407398670707/3125000000000 : ℝ)^3297 := by
    have hnat : (2112801159 : ℕ)^4321*3125000000000^3297 ≤ 407398670707^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112801159 10000000000 407398670707 3125000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048974353/2000000000 : ℝ)^4321 ≤ (42922857212229/100000000000000 : ℝ)^3297 := by
    have hnat : (1048974353 : ℕ)^4321*100000000000000^3297 ≤ 42922857212229^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048974353 2000000000 42922857212229 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337186733/2500000000 : ℝ), (-2112801159/10000000000 : ℝ), (1048974353/2000000000 : ℝ)] ![(22020192657367/50000000000000 : ℝ), (407398670707/3125000000000 : ℝ), (42922857212229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337186733/2500000000 : ℝ)|^4321 ≤ (22020192657367/50000000000000 : ℝ)^3297
        have hw : |(1337186733/2500000000 : ℝ)|=(1337186733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112801159/10000000000 : ℝ)|^4321 ≤ (407398670707/3125000000000 : ℝ)^3297
        have hw : |(-2112801159/10000000000 : ℝ)|=(2112801159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048974353/2000000000 : ℝ)|^4321 ≤ (42922857212229/100000000000000 : ℝ)^3297
        have hw : |(1048974353/2000000000 : ℝ)|=(1048974353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348746901/10000000000 : ℝ)*x 0 + (2622435919/5000000000 : ℝ)*x 1 + (-2112801103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348746901/10000000000 : ℝ)^4321 ≤ (44040384980211/100000000000000 : ℝ)^3297 := by
    have hnat : (5348746901 : ℕ)^4321*100000000000000^3297 ≤ 44040384980211^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348746901 10000000000 44040384980211 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622435919/5000000000 : ℝ)^4321 ≤ (21461428997597/50000000000000 : ℝ)^3297 := by
    have hnat : (2622435919 : ℕ)^4321*50000000000000^3297 ≤ 21461428997597^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622435919 5000000000 21461428997597 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112801103/10000000000 : ℝ)^4321 ≤ (13036757009763/100000000000000 : ℝ)^3297 := by
    have hnat : (2112801103 : ℕ)^4321*100000000000000^3297 ≤ 13036757009763^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112801103 10000000000 13036757009763 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348746901/10000000000 : ℝ), (2622435919/5000000000 : ℝ), (-2112801103/10000000000 : ℝ)] ![(44040384980211/100000000000000 : ℝ), (21461428997597/50000000000000 : ℝ), (13036757009763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348746901/10000000000 : ℝ)|^4321 ≤ (44040384980211/100000000000000 : ℝ)^3297
        have hw : |(5348746901/10000000000 : ℝ)|=(5348746901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622435919/5000000000 : ℝ)|^4321 ≤ (21461428997597/50000000000000 : ℝ)^3297
        have hw : |(2622435919/5000000000 : ℝ)|=(2622435919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112801103/10000000000 : ℝ)|^4321 ≤ (13036757009763/100000000000000 : ℝ)^3297
        have hw : |(-2112801103/10000000000 : ℝ)|=(2112801103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321652971/10000000000 : ℝ)*x 0 + (16205647/39062500 : ℝ)*x 1 + (4501328403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321652971/10000000000 : ℝ)^4321 ≤ (33303361571443/100000000000000 : ℝ)^3297 := by
    have hnat : (4321652971 : ℕ)^4321*100000000000000^3297 ≤ 33303361571443^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321652971 10000000000 33303361571443 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16205647/39062500 : ℝ)^4321 ≤ (31567023611347/100000000000000 : ℝ)^3297 := by
    have hnat : (16205647 : ℕ)^4321*100000000000000^3297 ≤ 31567023611347^3297*39062500^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16205647 39062500 31567023611347 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501328403/10000000000 : ℝ)^4321 ≤ (8782403703019/25000000000000 : ℝ)^3297 := by
    have hnat : (4501328403 : ℕ)^4321*25000000000000^3297 ≤ 8782403703019^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501328403 10000000000 8782403703019 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321652971/10000000000 : ℝ), (16205647/39062500 : ℝ), (4501328403/10000000000 : ℝ)] ![(33303361571443/100000000000000 : ℝ), (31567023611347/100000000000000 : ℝ), (8782403703019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321652971/10000000000 : ℝ)|^4321 ≤ (33303361571443/100000000000000 : ℝ)^3297
        have hw : |(4321652971/10000000000 : ℝ)|=(4321652971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16205647/39062500 : ℝ)|^4321 ≤ (31567023611347/100000000000000 : ℝ)^3297
        have hw : |(16205647/39062500 : ℝ)|=(16205647/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501328403/10000000000 : ℝ)|^4321 ≤ (8782403703019/25000000000000 : ℝ)^3297
        have hw : |(4501328403/10000000000 : ℝ)|=(4501328403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-20276411/100000000 : ℝ)*x 0 + (1311368377/2500000000 : ℝ)*x 1 + (1352862611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20276411/100000000 : ℝ)^4321 ≤ (6176218510263/50000000000000 : ℝ)^3297 := by
    have hnat : (20276411 : ℕ)^4321*50000000000000^3297 ≤ 6176218510263^3297*100000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20276411 100000000 6176218510263 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311368377/2500000000 : ℝ)^4321 ≤ (42929311344369/100000000000000 : ℝ)^3297 := by
    have hnat : (1311368377 : ℕ)^4321*100000000000000^3297 ≤ 42929311344369^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311368377 2500000000 42929311344369 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352862611/2500000000 : ℝ)^4321 ≤ (44718251615241/100000000000000 : ℝ)^3297 := by
    have hnat : (1352862611 : ℕ)^4321*100000000000000^3297 ≤ 44718251615241^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352862611 2500000000 44718251615241 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20276411/100000000 : ℝ), (1311368377/2500000000 : ℝ), (1352862611/2500000000 : ℝ)] ![(6176218510263/50000000000000 : ℝ), (42929311344369/100000000000000 : ℝ), (44718251615241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20276411/100000000 : ℝ)|^4321 ≤ (6176218510263/50000000000000 : ℝ)^3297
        have hw : |(-20276411/100000000 : ℝ)|=(20276411/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311368377/2500000000 : ℝ)|^4321 ≤ (42929311344369/100000000000000 : ℝ)^3297
        have hw : |(1311368377/2500000000 : ℝ)|=(1311368377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352862611/2500000000 : ℝ)|^4321 ≤ (44718251615241/100000000000000 : ℝ)^3297
        have hw : |(1352862611/2500000000 : ℝ)|=(1352862611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305591353/10000000000 : ℝ)*x 0 + (-1946222511/10000000000 : ℝ)*x 1 + (1082290091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305591353/10000000000 : ℝ)^4321 ≤ (10893818790499/25000000000000 : ℝ)^3297 := by
    have hnat : (5305591353 : ℕ)^4321*25000000000000^3297 ≤ 10893818790499^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305591353 10000000000 10893818790499 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946222511/10000000000 : ℝ)^4321 ≤ (585323654221/5000000000000 : ℝ)^3297 := by
    have hnat : (1946222511 : ℕ)^4321*5000000000000^3297 ≤ 585323654221^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946222511 10000000000 585323654221 5000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082290091/2000000000 : ℝ)^4321 ≤ (44718251734373/100000000000000 : ℝ)^3297 := by
    have hnat : (1082290091 : ℕ)^4321*100000000000000^3297 ≤ 44718251734373^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082290091 2000000000 44718251734373 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305591353/10000000000 : ℝ), (-1946222511/10000000000 : ℝ), (1082290091/2000000000 : ℝ)] ![(10893818790499/25000000000000 : ℝ), (585323654221/5000000000000 : ℝ), (44718251734373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305591353/10000000000 : ℝ)|^4321 ≤ (10893818790499/25000000000000 : ℝ)^3297
        have hw : |(5305591353/10000000000 : ℝ)|=(5305591353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1946222511/10000000000 : ℝ)|^4321 ≤ (585323654221/5000000000000 : ℝ)^3297
        have hw : |(-1946222511/10000000000 : ℝ)|=(1946222511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082290091/2000000000 : ℝ)|^4321 ≤ (44718251734373/100000000000000 : ℝ)^3297
        have hw : |(1082290091/2000000000 : ℝ)|=(1082290091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652795687/5000000000 : ℝ)*x 0 + (5411450423/10000000000 : ℝ)*x 1 + (-1946222527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652795687/5000000000 : ℝ)^4321 ≤ (43575275388039/100000000000000 : ℝ)^3297 := by
    have hnat : (2652795687 : ℕ)^4321*100000000000000^3297 ≤ 43575275388039^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652795687 5000000000 43575275388039 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411450423/10000000000 : ℝ)^4321 ≤ (22359125693903/50000000000000 : ℝ)^3297 := by
    have hnat : (5411450423 : ℕ)^4321*50000000000000^3297 ≤ 22359125693903^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411450423 10000000000 22359125693903 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1946222527/10000000000 : ℝ)^4321 ≤ (234129464211/2000000000000 : ℝ)^3297 := by
    have hnat : (1946222527 : ℕ)^4321*2000000000000^3297 ≤ 234129464211^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946222527 10000000000 234129464211 2000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652795687/5000000000 : ℝ), (5411450423/10000000000 : ℝ), (-1946222527/10000000000 : ℝ)] ![(43575275388039/100000000000000 : ℝ), (22359125693903/50000000000000 : ℝ), (234129464211/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652795687/5000000000 : ℝ)|^4321 ≤ (43575275388039/100000000000000 : ℝ)^3297
        have hw : |(2652795687/5000000000 : ℝ)|=(2652795687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411450423/10000000000 : ℝ)|^4321 ≤ (22359125693903/50000000000000 : ℝ)^3297
        have hw : |(5411450423/10000000000 : ℝ)|=(5411450423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1946222527/10000000000 : ℝ)|^4321 ≤ (234129464211/2000000000000 : ℝ)^3297
        have hw : |(-1946222527/10000000000 : ℝ)|=(1946222527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s5_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080419631/2500000000 : ℝ)*x 0 + (4500059069/10000000000 : ℝ)*x 1 + (829984309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080419631/2500000000 : ℝ)^4321 ≤ (33303619646359/100000000000000 : ℝ)^3297 := by
    have hnat : (1080419631 : ℕ)^4321*100000000000000^3297 ≤ 33303619646359^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080419631 2500000000 33303619646359 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500059069/10000000000 : ℝ)^4321 ≤ (35116632414607/100000000000000 : ℝ)^3297 := by
    have hnat : (4500059069 : ℕ)^4321*100000000000000^3297 ≤ 35116632414607^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500059069 10000000000 35116632414607 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829984309/2000000000 : ℝ)^4321 ≤ (31579747926489/100000000000000 : ℝ)^3297 := by
    have hnat : (829984309 : ℕ)^4321*100000000000000^3297 ≤ 31579747926489^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829984309 2000000000 31579747926489 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080419631/2500000000 : ℝ), (4500059069/10000000000 : ℝ), (829984309/2000000000 : ℝ)] ![(33303619646359/100000000000000 : ℝ), (35116632414607/100000000000000 : ℝ), (31579747926489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080419631/2500000000 : ℝ)|^4321 ≤ (33303619646359/100000000000000 : ℝ)^3297
        have hw : |(1080419631/2500000000 : ℝ)|=(1080419631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500059069/10000000000 : ℝ)|^4321 ≤ (35116632414607/100000000000000 : ℝ)^3297
        have hw : |(4500059069/10000000000 : ℝ)|=(4500059069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829984309/2000000000 : ℝ)|^4321 ≤ (31579747926489/100000000000000 : ℝ)^3297
        have hw : |(829984309/2000000000 : ℝ)|=(829984309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1361_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5593/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7363/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11149/100000 : ℝ) ^ (135/32 : ℝ) ≤ (9561510765364671/100000000000000000000 : ℝ) := by
    have hpowers : (11149/100000 : ℝ)^135 ≤ (9561510765364671/100000000000000000000 : ℝ)^32 := by
      have hnat : (11149 : ℕ)^135*100000000000000000000^32 ≤ 9561510765364671^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11149 100000 9561510765364671 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11149/100000 : ℝ)) (X := (9561510765364671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (135/32 : ℝ) ≤ (15642195597094263/50000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^135 ≤ (15642195597094263/50000000000000000000 : ℝ)^32 := by
      have hnat : (7383 : ℕ)^135*50000000000000000000^32 ≤ 15642195597094263^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 15642195597094263 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (15642195597094263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009561510765364671/50000000000000000000 : ℝ) ≤ (5000226626686199/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (50009561510765364671/50000000000000000000 : ℝ)^32 ≤ (5000226626686199/5000000000000000 : ℝ)^135 := by
      have hnat : (50009561510765364671 : ℕ)^32*5000000000000000^135 ≤ 5000226626686199^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009561510765364671 50000000000000000000 5000226626686199 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000226626686199/5000000000000000 : ℝ)) (X := (50009561510765364671/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040845901959553197/100000000000000000000 : ℝ) ≤ (2500242012082351/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (100040845901959553197/100000000000000000000 : ℝ)^32 ≤ (2500242012082351/2500000000000000 : ℝ)^135 := by
      have hnat : (100040845901959553197 : ℕ)^32*2500000000000000^135 ≤ 2500242012082351^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040845901959553197 100000000000000000000 2500242012082351 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500242012082351/2500000000000000 : ℝ)) (X := (100040845901959553197/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015642195597094263/25000000000000000000 : ℝ) ≤ (1000148284328641/1000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (25015642195597094263/25000000000000000000 : ℝ)^32 ≤ (1000148284328641/1000000000000000 : ℝ)^135 := by
      have hnat : (25015642195597094263 : ℕ)^32*1000000000000000^135 ≤ 1000148284328641^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015642195597094263 25000000000000000000 1000148284328641 1000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000148284328641/1000000000000000 : ℝ)) (X := (25015642195597094263/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9561510765364671/100000000000000000000 : ℝ) ≤ ((18080080259748321889/18085000000000000000 : ℝ)+2*(257397478503/180850000000000 : ℝ)*(11149/100000 : ℝ))^(135/32 : ℝ) := by
    rw [show (18080080259748321889/18085000000000000000 : ℝ)+2*(257397478503/180850000000000 : ℝ)*(11149/100000 : ℝ)=(5000226626686199/5000000000000000 : ℝ) by norm_num, show 1+2*(9561510765364671/100000000000000000000 : ℝ)=(50009561510765364671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15642195597094263/50000000000000000000 : ℝ)+(9561510765364671/100000000000000000000 : ℝ) ≤ ((18080080259748321889/18085000000000000000 : ℝ)+(257397478503/180850000000000 : ℝ)*((7383/50000 : ℝ)+(11149/100000 : ℝ)))^(135/32 : ℝ) := by
    rw [show (18080080259748321889/18085000000000000000 : ℝ)+(257397478503/180850000000000 : ℝ)*((7383/50000 : ℝ)+(11149/100000 : ℝ))=(2500242012082351/2500000000000000 : ℝ) by norm_num, show 1+(15642195597094263/50000000000000000000 : ℝ)+(9561510765364671/100000000000000000000 : ℝ)=(100040845901959553197/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15642195597094263/50000000000000000000 : ℝ) ≤ ((18080080259748321889/18085000000000000000 : ℝ)+2*(257397478503/180850000000000 : ℝ)*(7383/50000 : ℝ))^(135/32 : ℝ) := by
    rw [show (18080080259748321889/18085000000000000000 : ℝ)+2*(257397478503/180850000000000 : ℝ)*(7383/50000 : ℝ)=(1000148284328641/1000000000000000 : ℝ) by norm_num, show 1+2*(15642195597094263/50000000000000000000 : ℝ)=(25015642195597094263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18080080259748321889/18085000000000000000 : ℝ)*(X 1 0+X 2 0)+(257397478503/180850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (18080080259748321889/18085000000000000000 : ℝ)) (alpha := (257397478503/180850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18080080259748321889/18085000000000000000 : ℝ)*(X 0 1+X 2 1)+(257397478503/180850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (18080080259748321889/18085000000000000000 : ℝ)) (alpha := (257397478503/180850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18080080259748321889/18085000000000000000 : ℝ)*(X 0 2+X 1 2)+(257397478503/180850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (18080080259748321889/18085000000000000000 : ℝ)) (alpha := (257397478503/180850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2027629049/10000000000 : ℝ)*X 0 0+(5412055297/10000000000 : ℝ)*X 0 1+(1311217931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337186733/2500000000 : ℝ)*X 1 0+(-2112801159/10000000000 : ℝ)*X 1 1+(1048974353/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348746901/10000000000 : ℝ)*X 2 0+(2622435919/5000000000 : ℝ)*X 2 1+(-2112801103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321652971/10000000000 : ℝ)*X 0 0+(16205647/39062500 : ℝ)*X 0 1+(4501328403/10000000000 : ℝ)*X 0 2+(4321652971/10000000000 : ℝ)*X 1 0+(16205647/39062500 : ℝ)*X 1 1+(4501328403/10000000000 : ℝ)*X 1 2+(4321652971/10000000000 : ℝ)*X 2 0+(16205647/39062500 : ℝ)*X 2 1+(4501328403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-20276411/100000000 : ℝ)*X 0 0+(1311368377/2500000000 : ℝ)*X 0 1+(1352862611/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305591353/10000000000 : ℝ)*X 1 0+(-1946222511/10000000000 : ℝ)*X 1 1+(1082290091/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652795687/5000000000 : ℝ)*X 2 0+(5411450423/10000000000 : ℝ)*X 2 1+(-1946222527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080419631/2500000000 : ℝ)*X 0 0+(4500059069/10000000000 : ℝ)*X 0 1+(829984309/2000000000 : ℝ)*X 0 2+(1080419631/2500000000 : ℝ)*X 1 0+(4500059069/10000000000 : ℝ)*X 1 1+(829984309/2000000000 : ℝ)*X 1 2+(1080419631/2500000000 : ℝ)*X 2 0+(4500059069/10000000000 : ℝ)*X 2 1+(829984309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4432371831235180366035833721/452125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1982380503/100000000000000 : ℝ)*(base19) + (1916744933/100000000000000 : ℝ)*(base23) + (16564043/100000000000000 : ℝ)*(lower2) + (103193417/50000000000000 : ℝ)*(upper3) + (123097739/50000000000000 : ℝ)*(upper5) + (2204247102996721/50000000000000 : ℝ)*(major0) + (2204247102996721/50000000000000 : ℝ)*(major1) + (2204247102996721/50000000000000 : ℝ)*(major2) + (5981492612460219/100000000000000 : ℝ)*(sp0) + (5981536301268857/100000000000000 : ℝ)*(sp1) + (5981536366904427/100000000000000 : ℝ)*(sp2) + (1417714875990239/50000000000000 : ℝ)*(sp3) + (22835594571/50000000000000 : ℝ)*(sp4) + (20049576329/100000000000000 : ℝ)*(sp7) + (2835449801556807/100000000000000 : ℝ)*(f.failure) + (74769228545617/1250000000000 : ℝ)*(f.sum) + (16418717150603/18085000000000000000000000000 : ℝ)*base66 + (11598655834112174031/904250000000000000000000000000000 : ℝ)*base68 + (14217021636071924031/904250000000000000000000000000000 : ℝ)*base70 + (6501602295360674031/904250000000000000000000000000000 : ℝ)*base72 + (57594284471369/9042500000000000000000000000 : ℝ)*base74 + (12916073544976174031/904250000000000000000000000000000 : ℝ)*base76 + (3150030417573424031/904250000000000000000000000000000 : ℝ)*base78 + (6852108914661924031/904250000000000000000000000000000 : ℝ)*base80 + (7395090572111/9042500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (85350811/10000000000000000000000 : ℝ)*base89 + (85350811/10000000000000000000000 : ℝ)*base91 + (85350811/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1667277170216244517529436363/226062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1310837971/100000000000000 : ℝ)*(base19) + (1411182251/100000000000000 : ℝ)*(base23) + (76751443/50000000000000 : ℝ)*(upper3) + (18569077/50000000000000 : ℝ)*(lower4) + (16041693/10000000000000 : ℝ)*(upper5) + (2220238424548911/50000000000000 : ℝ)*(major0) + (2220238424548911/50000000000000 : ℝ)*(major1) + (2220238424548911/50000000000000 : ℝ)*(major2) + (6822737007/25000000000000 : ℝ)*(sp1) + (2808996623/10000000000000 : ℝ)*(sp2) + (301246654715929/5000000000000 : ℝ)*(sp4) + (301245224626629/5000000000000 : ℝ)*(sp5) + (6024903593170099/100000000000000 : ℝ)*(sp6) + (714005089508489/25000000000000 : ℝ)*(sp7) + (714005089508489/25000000000000 : ℝ)*(f.failure) + (301246654715929/5000000000000 : ℝ)*(f.sum) + (12492493050327/4521250000000000000000000000 : ℝ)*base66 + (5610248302658712879/904250000000000000000000000000000 : ℝ)*base67 + (1469953460030712879/904250000000000000000000000000000 : ℝ)*base69 + (7219030063010712879/904250000000000000000000000000000 : ℝ)*base71 + (537015131817/282578125000000000000000000 : ℝ)*base74 + (939424101119287121/904250000000000000000000000000000 : ℝ)*base76 + (8285097029225712879/904250000000000000000000000000000 : ℝ)*base77 + (9642883218956462879/904250000000000000000000000000000 : ℝ)*base79 + (46851923551587/18085000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (15685003/2500000000000000000000 : ℝ)*base90 + (15685003/2500000000000000000000 : ℝ)*base92 + (15685003/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1361_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1361_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1361_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1361_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1361_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1361_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1361_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

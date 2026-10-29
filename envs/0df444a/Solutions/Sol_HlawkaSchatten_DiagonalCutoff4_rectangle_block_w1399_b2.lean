-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:47.254084+00:00
-- url     : https://prove2.me/submissions/4aa92492-516c-4c24-af24-f28035e99a6a

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
theorem support_rectangle_w1399_s6_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-498933239/2500000000 : ℝ)*x 0 + (5409773419/10000000000 : ℝ)*x 1 + (5246188853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498933239/2500000000 : ℝ)^4359 ≤ (12167499742231/100000000000000 : ℝ)^3335 := by
    have hnat : (498933239 : ℕ)^4359*100000000000000^3335 ≤ 12167499742231^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498933239 2500000000 12167499742231 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409773419/10000000000 : ℝ)^4359 ≤ (44797383726153/100000000000000 : ℝ)^3335 := by
    have hnat : (5409773419 : ℕ)^4359*100000000000000^3335 ≤ 44797383726153^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409773419 10000000000 44797383726153 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246188853/10000000000 : ℝ)^4359 ≤ (21517558256959/50000000000000 : ℝ)^3335 := by
    have hnat : (5246188853 : ℕ)^4359*50000000000000^3335 ≤ 21517558256959^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246188853 10000000000 21517558256959 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498933239/2500000000 : ℝ), (5409773419/10000000000 : ℝ), (5246188853/10000000000 : ℝ)] ![(12167499742231/100000000000000 : ℝ), (44797383726153/100000000000000 : ℝ), (21517558256959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498933239/2500000000 : ℝ)|^4359 ≤ (12167499742231/100000000000000 : ℝ)^3335
        have hw : |(-498933239/2500000000 : ℝ)|=(498933239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409773419/10000000000 : ℝ)|^4359 ≤ (44797383726153/100000000000000 : ℝ)^3335
        have hw : |(5409773419/10000000000 : ℝ)|=(5409773419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246188853/10000000000 : ℝ)|^4359 ≤ (21517558256959/50000000000000 : ℝ)^3335
        have hw : |(5246188853/10000000000 : ℝ)|=(5246188853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673971189/5000000000 : ℝ)*x 0 + (-259879671/1250000000 : ℝ)*x 1 + (2623094461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673971189/5000000000 : ℝ)^4359 ≤ (44129337652893/100000000000000 : ℝ)^3335 := by
    have hnat : (2673971189 : ℕ)^4359*100000000000000^3335 ≤ 44129337652893^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673971189 5000000000 44129337652893 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259879671/1250000000 : ℝ)^4359 ≤ (2567109016229/20000000000000 : ℝ)^3335 := by
    have hnat : (259879671 : ℕ)^4359*20000000000000^3335 ≤ 2567109016229^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259879671 1250000000 2567109016229 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623094461/5000000000 : ℝ)^4359 ≤ (43035117253727/100000000000000 : ℝ)^3335 := by
    have hnat : (2623094461 : ℕ)^4359*100000000000000^3335 ≤ 43035117253727^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623094461 5000000000 43035117253727 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673971189/5000000000 : ℝ), (-259879671/1250000000 : ℝ), (2623094461/5000000000 : ℝ)] ![(44129337652893/100000000000000 : ℝ), (2567109016229/20000000000000 : ℝ), (43035117253727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673971189/5000000000 : ℝ)|^4359 ≤ (44129337652893/100000000000000 : ℝ)^3335
        have hw : |(2673971189/5000000000 : ℝ)|=(2673971189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259879671/1250000000 : ℝ)|^4359 ≤ (2567109016229/20000000000000 : ℝ)^3335
        have hw : |(-259879671/1250000000 : ℝ)|=(259879671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623094461/5000000000 : ℝ)|^4359 ≤ (43035117253727/100000000000000 : ℝ)^3335
        have hw : |(2623094461/5000000000 : ℝ)|=(2623094461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347941963/10000000000 : ℝ)*x 0 + (262309459/500000000 : ℝ)*x 1 + (-2079037579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347941963/10000000000 : ℝ)^4359 ≤ (44129333176999/100000000000000 : ℝ)^3335 := by
    have hnat : (5347941963 : ℕ)^4359*100000000000000^3335 ≤ 44129333176999^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347941963 10000000000 44129333176999 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262309459/500000000 : ℝ)^4359 ≤ (21517560009983/50000000000000 : ℝ)^3335 := by
    have hnat : (262309459 : ℕ)^4359*50000000000000^3335 ≤ 21517560009983^3335*500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262309459 500000000 21517560009983 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079037579/10000000000 : ℝ)^4359 ≤ (3208886695949/25000000000000 : ℝ)^3335 := by
    have hnat : (2079037579 : ℕ)^4359*25000000000000^3335 ≤ 3208886695949^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079037579 10000000000 3208886695949 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347941963/10000000000 : ℝ), (262309459/500000000 : ℝ), (-2079037579/10000000000 : ℝ)] ![(44129333176999/100000000000000 : ℝ), (21517560009983/50000000000000 : ℝ), (3208886695949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347941963/10000000000 : ℝ)|^4359 ≤ (44129333176999/100000000000000 : ℝ)^3335
        have hw : |(5347941963/10000000000 : ℝ)|=(5347941963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262309459/500000000 : ℝ)|^4359 ≤ (21517560009983/50000000000000 : ℝ)^3335
        have hw : |(262309459/500000000 : ℝ)|=(262309459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079037579/10000000000 : ℝ)|^4359 ≤ (3208886695949/25000000000000 : ℝ)^3335
        have hw : |(-2079037579/10000000000 : ℝ)|=(2079037579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077982977/2500000000 : ℝ)*x 0 + (2070083609/5000000000 : ℝ)*x 1 + (4490169249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077982977/2500000000 : ℝ)^4359 ≤ (6660842765819/20000000000000 : ℝ)^3335 := by
    have hnat : (1077982977 : ℕ)^4359*20000000000000^3335 ≤ 6660842765819^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077982977 2500000000 6660842765819 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070083609/5000000000 : ℝ)^4359 ≤ (31580905082383/100000000000000 : ℝ)^3335 := by
    have hnat : (2070083609 : ℕ)^4359*100000000000000^3335 ≤ 31580905082383^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070083609 5000000000 31580905082383 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490169249/10000000000 : ℝ)^4359 ≤ (1097340033649/3125000000000 : ℝ)^3335 := by
    have hnat : (4490169249 : ℕ)^4359*3125000000000^3335 ≤ 1097340033649^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490169249 10000000000 1097340033649 3125000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077982977/2500000000 : ℝ), (2070083609/5000000000 : ℝ), (4490169249/10000000000 : ℝ)] ![(6660842765819/20000000000000 : ℝ), (31580905082383/100000000000000 : ℝ), (1097340033649/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077982977/2500000000 : ℝ)|^4359 ≤ (6660842765819/20000000000000 : ℝ)^3335
        have hw : |(1077982977/2500000000 : ℝ)|=(1077982977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070083609/5000000000 : ℝ)|^4359 ≤ (31580905082383/100000000000000 : ℝ)^3335
        have hw : |(2070083609/5000000000 : ℝ)|=(2070083609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490169249/10000000000 : ℝ)|^4359 ≤ (1097340033649/3125000000000 : ℝ)^3335
        have hw : |(4490169249/10000000000 : ℝ)|=(4490169249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249467987/1250000000 : ℝ)*x 0 + (163961799/312500000 : ℝ)*x 1 + (2704591077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249467987/1250000000 : ℝ)^4359 ≤ (6083793460189/50000000000000 : ℝ)^3335 := by
    have hnat : (249467987 : ℕ)^4359*50000000000000^3335 ≤ 6083793460189^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249467987 1250000000 6083793460189 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163961799/312500000 : ℝ)^4359 ≤ (4304142874191/10000000000000 : ℝ)^3335 := by
    have hnat : (163961799 : ℕ)^4359*10000000000000^3335 ≤ 4304142874191^3335*312500000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163961799 312500000 4304142874191 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704591077/5000000000 : ℝ)^4359 ≤ (11197746080679/25000000000000 : ℝ)^3335 := by
    have hnat : (2704591077 : ℕ)^4359*25000000000000^3335 ≤ 11197746080679^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704591077 5000000000 11197746080679 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249467987/1250000000 : ℝ), (163961799/312500000 : ℝ), (2704591077/5000000000 : ℝ)] ![(6083793460189/50000000000000 : ℝ), (4304142874191/10000000000000 : ℝ), (11197746080679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249467987/1250000000 : ℝ)|^4359 ≤ (6083793460189/50000000000000 : ℝ)^3335
        have hw : |(-249467987/1250000000 : ℝ)|=(249467987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163961799/312500000 : ℝ)|^4359 ≤ (4304142874191/10000000000000 : ℝ)^3335
        have hw : |(163961799/312500000 : ℝ)|=(163961799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704591077/5000000000 : ℝ)|^4359 ≤ (11197746080679/25000000000000 : ℝ)^3335
        have hw : |(2704591077/5000000000 : ℝ)|=(2704591077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652771293/5000000000 : ℝ)*x 0 + (-1916044607/10000000000 : ℝ)*x 1 + (2704591147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652771293/5000000000 : ℝ)^4359 ≤ (1091815033487/2500000000000 : ℝ)^3335 := by
    have hnat : (2652771293 : ℕ)^4359*2500000000000^3335 ≤ 1091815033487^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652771293 5000000000 1091815033487 2500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916044607/10000000000 : ℝ)^4359 ≤ (288410320237/2500000000000 : ℝ)^3335 := by
    have hnat : (1916044607 : ℕ)^4359*2500000000000^3335 ≤ 288410320237^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916044607 10000000000 288410320237 2500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704591147/5000000000 : ℝ)^4359 ≤ (5598873229743/12500000000000 : ℝ)^3335 := by
    have hnat : (2704591147 : ℕ)^4359*12500000000000^3335 ≤ 5598873229743^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704591147 5000000000 5598873229743 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652771293/5000000000 : ℝ), (-1916044607/10000000000 : ℝ), (2704591147/5000000000 : ℝ)] ![(1091815033487/2500000000000 : ℝ), (288410320237/2500000000000 : ℝ), (5598873229743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652771293/5000000000 : ℝ)|^4359 ≤ (1091815033487/2500000000000 : ℝ)^3335
        have hw : |(2652771293/5000000000 : ℝ)|=(2652771293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916044607/10000000000 : ℝ)|^4359 ≤ (288410320237/2500000000000 : ℝ)^3335
        have hw : |(-1916044607/10000000000 : ℝ)|=(1916044607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704591147/5000000000 : ℝ)|^4359 ≤ (5598873229743/12500000000000 : ℝ)^3335
        have hw : |(2704591147/5000000000 : ℝ)|=(2704591147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652771349/5000000000 : ℝ)*x 0 + (2704591039/5000000000 : ℝ)*x 1 + (-1916044751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652771349/5000000000 : ℝ)^4359 ≤ (43672602544483/100000000000000 : ℝ)^3335 := by
    have hnat : (2652771349 : ℕ)^4359*100000000000000^3335 ≤ 43672602544483^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652771349 5000000000 43672602544483 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704591039/5000000000 : ℝ)^4359 ≤ (44790983500163/100000000000000 : ℝ)^3335 := by
    have hnat : (2704591039 : ℕ)^4359*100000000000000^3335 ≤ 44790983500163^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704591039 5000000000 44790983500163 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916044751/10000000000 : ℝ)^4359 ≤ (1442051742839/12500000000000 : ℝ)^3335 := by
    have hnat : (1916044751 : ℕ)^4359*12500000000000^3335 ≤ 1442051742839^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916044751 10000000000 1442051742839 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652771349/5000000000 : ℝ), (2704591039/5000000000 : ℝ), (-1916044751/10000000000 : ℝ)] ![(43672602544483/100000000000000 : ℝ), (44790983500163/100000000000000 : ℝ), (1442051742839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652771349/5000000000 : ℝ)|^4359 ≤ (43672602544483/100000000000000 : ℝ)^3335
        have hw : |(2652771349/5000000000 : ℝ)|=(2652771349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704591039/5000000000 : ℝ)|^4359 ≤ (44790983500163/100000000000000 : ℝ)^3335
        have hw : |(2704591039/5000000000 : ℝ)|=(2704591039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916044751/10000000000 : ℝ)|^4359 ≤ (1442051742839/12500000000000 : ℝ)^3335
        have hw : |(-1916044751/10000000000 : ℝ)|=(1916044751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s6_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311956761/10000000000 : ℝ)*x 0 + (897781979/2000000000 : ℝ)*x 1 + (2070716533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311956761/10000000000 : ℝ)^4359 ≤ (8326116181821/25000000000000 : ℝ)^3335 := by
    have hnat : (4311956761 : ℕ)^4359*25000000000000^3335 ≤ 8326116181821^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311956761 10000000000 8326116181821 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897781979/2000000000 : ℝ)^4359 ≤ (1404080359971/4000000000000 : ℝ)^3335 := by
    have hnat : (897781979 : ℕ)^4359*4000000000000^3335 ≤ 1404080359971^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897781979 2000000000 1404080359971 4000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070716533/5000000000 : ℝ)^4359 ≤ (31593526253771/100000000000000 : ℝ)^3335 := by
    have hnat : (2070716533 : ℕ)^4359*100000000000000^3335 ≤ 31593526253771^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070716533 5000000000 31593526253771 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311956761/10000000000 : ℝ), (897781979/2000000000 : ℝ), (2070716533/5000000000 : ℝ)] ![(8326116181821/25000000000000 : ℝ), (1404080359971/4000000000000 : ℝ), (31593526253771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311956761/10000000000 : ℝ)|^4359 ≤ (8326116181821/25000000000000 : ℝ)^3335
        have hw : |(4311956761/10000000000 : ℝ)|=(4311956761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897781979/2000000000 : ℝ)|^4359 ≤ (1404080359971/4000000000000 : ℝ)^3335
        have hw : |(897781979/2000000000 : ℝ)|=(897781979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070716533/5000000000 : ℝ)|^4359 ≤ (31593526253771/100000000000000 : ℝ)^3335
        have hw : |(2070716533/5000000000 : ℝ)|=(2070716533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (2179/512 : ℝ) ≤ (9235267592561573/100000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^2179 ≤ (9235267592561573/100000000000000000000 : ℝ)^512 := by
      have hnat : (1409 : ℕ)^2179*100000000000000000000^512 ≤ 9235267592561573^512*12500^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 9235267592561573 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (9235267592561573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7373/50000 : ℝ) ^ (2179/512 : ℝ) ≤ (28973064031610687/100000000000000000000 : ℝ) := by
    have hpowers : (7373/50000 : ℝ)^2179 ≤ (28973064031610687/100000000000000000000 : ℝ)^512 := by
      have hnat : (7373 : ℕ)^2179*100000000000000000000^512 ≤ 28973064031610687^512*50000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7373 50000 28973064031610687 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7373/50000 : ℝ)) (X := (28973064031610687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009235267592561573/50000000000000000000 : ℝ) ≤ (10000433971818829/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50009235267592561573/50000000000000000000 : ℝ)^512 ≤ (10000433971818829/10000000000000000 : ℝ)^2179 := by
      have hnat : (50009235267592561573 : ℕ)^512*10000000000000000^2179 ≤ 10000433971818829^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009235267592561573 50000000000000000000 10000433971818829 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433971818829/10000000000000000 : ℝ)) (X := (50009235267592561573/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001910416581208613/5000000000000000000 : ℝ) ≤ (2500224412658333/2500000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (5001910416581208613/5000000000000000000 : ℝ)^512 ≤ (2500224412658333/2500000000000000 : ℝ)^2179 := by
      have hnat : (5001910416581208613 : ℕ)^512*2500000000000000^2179 ≤ 2500224412658333^2179*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001910416581208613 5000000000000000000 2500224412658333 2500000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500224412658333/2500000000000000 : ℝ)) (X := (5001910416581208613/5000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028973064031610687/50000000000000000000 : ℝ) ≤ (2000272265889567/2000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50028973064031610687/50000000000000000000 : ℝ)^512 ≤ (2000272265889567/2000000000000000 : ℝ)^2179 := by
      have hnat : (50028973064031610687 : ℕ)^512*2000000000000000^2179 ≤ 2000272265889567^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028973064031610687 50000000000000000000 2000272265889567 2000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000272265889567/2000000000000000 : ℝ)) (X := (50028973064031610687/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9235267592561573/100000000000000000000 : ℝ) ≤ ((17365527221452228157/17370000000000000000 : ℝ)+2*(463678814503/347400000000000 : ℝ)*(1409/12500 : ℝ))^(2179/512 : ℝ) := by
    rw [show (17365527221452228157/17370000000000000000 : ℝ)+2*(463678814503/347400000000000 : ℝ)*(1409/12500 : ℝ)=(10000433971818829/10000000000000000 : ℝ) by norm_num, show 1+2*(9235267592561573/100000000000000000000 : ℝ)=(50009235267592561573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28973064031610687/100000000000000000000 : ℝ)+(9235267592561573/100000000000000000000 : ℝ) ≤ ((17365527221452228157/17370000000000000000 : ℝ)+(463678814503/347400000000000 : ℝ)*((7373/50000 : ℝ)+(1409/12500 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (17365527221452228157/17370000000000000000 : ℝ)+(463678814503/347400000000000 : ℝ)*((7373/50000 : ℝ)+(1409/12500 : ℝ))=(2500224412658333/2500000000000000 : ℝ) by norm_num, show 1+(28973064031610687/100000000000000000000 : ℝ)+(9235267592561573/100000000000000000000 : ℝ)=(5001910416581208613/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28973064031610687/100000000000000000000 : ℝ) ≤ ((17365527221452228157/17370000000000000000 : ℝ)+2*(463678814503/347400000000000 : ℝ)*(7373/50000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (17365527221452228157/17370000000000000000 : ℝ)+2*(463678814503/347400000000000 : ℝ)*(7373/50000 : ℝ)=(2000272265889567/2000000000000000 : ℝ) by norm_num, show 1+2*(28973064031610687/100000000000000000000 : ℝ)=(50028973064031610687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17365527221452228157/17370000000000000000 : ℝ)*(X 1 0+X 2 0)+(463678814503/347400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (17365527221452228157/17370000000000000000 : ℝ)) (alpha := (463678814503/347400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17365527221452228157/17370000000000000000 : ℝ)*(X 0 1+X 2 1)+(463678814503/347400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (17365527221452228157/17370000000000000000 : ℝ)) (alpha := (463678814503/347400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17365527221452228157/17370000000000000000 : ℝ)*(X 0 2+X 1 2)+(463678814503/347400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (17365527221452228157/17370000000000000000 : ℝ)) (alpha := (463678814503/347400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-498933239/2500000000 : ℝ)*X 0 0+(5409773419/10000000000 : ℝ)*X 0 1+(5246188853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673971189/5000000000 : ℝ)*X 1 0+(-259879671/1250000000 : ℝ)*X 1 1+(2623094461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347941963/10000000000 : ℝ)*X 2 0+(262309459/500000000 : ℝ)*X 2 1+(-2079037579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077982977/2500000000 : ℝ)*X 0 0+(2070083609/5000000000 : ℝ)*X 0 1+(4490169249/10000000000 : ℝ)*X 0 2+(1077982977/2500000000 : ℝ)*X 1 0+(2070083609/5000000000 : ℝ)*X 1 1+(4490169249/10000000000 : ℝ)*X 1 2+(1077982977/2500000000 : ℝ)*X 2 0+(2070083609/5000000000 : ℝ)*X 2 1+(4490169249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-249467987/1250000000 : ℝ)*X 0 0+(163961799/312500000 : ℝ)*X 0 1+(2704591077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652771293/5000000000 : ℝ)*X 1 0+(-1916044607/10000000000 : ℝ)*X 1 1+(2704591147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652771349/5000000000 : ℝ)*X 2 0+(2704591039/5000000000 : ℝ)*X 2 1+(-1916044751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311956761/10000000000 : ℝ)*X 0 0+(897781979/2000000000 : ℝ)*X 0 1+(2070716533/5000000000 : ℝ)*X 0 2+(4311956761/10000000000 : ℝ)*X 1 0+(897781979/2000000000 : ℝ)*X 1 1+(2070716533/5000000000 : ℝ)*X 1 2+(4311956761/10000000000 : ℝ)*X 2 0+(897781979/2000000000 : ℝ)*X 2 1+(2070716533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224305385341091910016969683/48250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1463183779/100000000000000 : ℝ)*(base19) + (985851383/100000000000000 : ℝ)*(base23) + (118599/195312500000 : ℝ)*(upper2) + (87148201/25000000000000 : ℝ)*(upper3) + (12460649/20000000000000 : ℝ)*(upper4) + (2242566769617119/50000000000000 : ℝ)*(major0) + (2242566769617119/50000000000000 : ℝ)*(major1) + (2242566769617119/50000000000000 : ℝ)*(major2) + (6113086924607677/100000000000000 : ℝ)*(sp0) + (3056554668551883/50000000000000 : ℝ)*(sp1) + (3056554907218081/50000000000000 : ℝ)*(sp2) + (2857139420662257/100000000000000 : ℝ)*(sp3) + (23875679869/100000000000000 : ℝ)*(sp4) + (3340511623/20000000000000 : ℝ)*(sp7) + (714289030805093/25000000000000 : ℝ)*(f.failure) + (3056555400143773/50000000000000 : ℝ)*(f.sum) + (46181777196059/4342500000000000000000000000 : ℝ)*base66 + (13961963940247130317/868500000000000000000000000000000 : ℝ)*base68 + (18985361586301130317/868500000000000000000000000000000 : ℝ)*base70 + (9553112462237630317/868500000000000000000000000000000 : ℝ)*base72 + (17768287402649/4342500000000000000000000000 : ℝ)*base74 + (3583554501533630317/868500000000000000000000000000000 : ℝ)*base76 + (14737771255010630317/868500000000000000000000000000000 : ℝ)*base78 + (18676886211239630317/868500000000000000000000000000000 : ℝ)*base80 + (18089424536467/2171250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9953377/500000000000000000000 : ℝ)*base89 + (9953377/500000000000000000000 : ℝ)*base91 + (9953377/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3562621828089094940418941/463200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (437951/3125000000000 : ℝ)*(base23) + (169743691/100000000000000 : ℝ)*(lower2) + (8905371/6250000000000 : ℝ)*(lower4) + (63348891/100000000000000 : ℝ)*(upper5) + (7228288244287/160000000000 : ℝ)*(major0) + (7228288244287/160000000000 : ℝ)*(major1) + (7228288244287/160000000000 : ℝ)*(major2) + (175869777/6250000000000 : ℝ)*(sp0) + (1012844439/12500000000000 : ℝ)*(sp1) + (20052181/100000000000000 : ℝ)*(sp2) + (769683500540989/12500000000000 : ℝ)*(sp4) + (6157462715488833/100000000000000 : ℝ)*(sp5) + (1539367696044433/25000000000000 : ℝ)*(sp6) + (719472307684221/25000000000000 : ℝ)*(sp7) + (719472307684221/25000000000000 : ℝ)*(f.failure) + (1231494163648869/20000000000000 : ℝ)*(f.sum) + (27264132851159/694800000000000000000000000 : ℝ)*base66 + (1971160799682259/2779200000000000000000000000000 : ℝ)*base67 + (17041775550229459/2779200000000000000000000000000 : ℝ)*base69 + (128370187889317459/2779200000000000000000000000000 : ℝ)*base71 + (12742169420917/3474000000000000000000000000 : ℝ)*base74 + (4366550205887059/2779200000000000000000000000000 : ℝ)*base75 + (48607996807330541/2779200000000000000000000000000 : ℝ)*base78 + (15203988521156141/2779200000000000000000000000000 : ℝ)*base80 + (13364330443237/3474000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6145369/500000000000000000000 : ℝ)*base89 + (6145369/500000000000000000000 : ℝ)*base91 + (6145369/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1399_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1399_s7_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1995736271/10000000000 : ℝ)*x 0 + (2704867859/5000000000 : ℝ)*x 1 + (81972257/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995736271/10000000000 : ℝ)^4359 ≤ (12167526158629/100000000000000 : ℝ)^3335 := by
    have hnat : (1995736271 : ℕ)^4359*100000000000000^3335 ≤ 12167526158629^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995736271 10000000000 12167526158629 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704867859/5000000000 : ℝ)^4359 ≤ (44796975672743/100000000000000 : ℝ)^3335 := by
    have hnat : (2704867859 : ℕ)^4359*100000000000000^3335 ≤ 44796975672743^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704867859 5000000000 44796975672743 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81972257/156250000 : ℝ)^4359 ≤ (43035498158889/100000000000000 : ℝ)^3335 := by
    have hnat : (81972257 : ℕ)^4359*100000000000000^3335 ≤ 43035498158889^3335*156250000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81972257 156250000 43035498158889 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1995736271/10000000000 : ℝ), (2704867859/5000000000 : ℝ), (81972257/156250000 : ℝ)] ![(12167526158629/100000000000000 : ℝ), (44796975672743/100000000000000 : ℝ), (43035498158889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1995736271/10000000000 : ℝ)|^4359 ≤ (12167526158629/100000000000000 : ℝ)^3335
        have hw : |(-1995736271/10000000000 : ℝ)|=(1995736271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704867859/5000000000 : ℝ)|^4359 ≤ (44796975672743/100000000000000 : ℝ)^3335
        have hw : |(2704867859/5000000000 : ℝ)|=(2704867859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81972257/156250000 : ℝ)|^4359 ≤ (43035498158889/100000000000000 : ℝ)^3335
        have hw : |(81972257/156250000 : ℝ)|=(81972257/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347932573/10000000000 : ℝ)*x 0 + (-2079003309/10000000000 : ℝ)*x 1 + (5246224419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347932573/10000000000 : ℝ)^4359 ≤ (2206461595159/5000000000000 : ℝ)^3335 := by
    have hnat : (5347932573 : ℕ)^4359*5000000000000^3335 ≤ 2206461595159^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347932573 10000000000 2206461595159 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079003309/10000000000 : ℝ)^4359 ≤ (6417635122499/50000000000000 : ℝ)^3335 := by
    have hnat : (2079003309 : ℕ)^4359*50000000000000^3335 ≤ 6417635122499^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079003309 10000000000 6417635122499 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246224419/10000000000 : ℝ)^4359 ≤ (21517748923977/50000000000000 : ℝ)^3335 := by
    have hnat : (5246224419 : ℕ)^4359*50000000000000^3335 ≤ 21517748923977^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246224419 10000000000 21517748923977 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347932573/10000000000 : ℝ), (-2079003309/10000000000 : ℝ), (5246224419/10000000000 : ℝ)] ![(2206461595159/5000000000000 : ℝ), (6417635122499/50000000000000 : ℝ), (21517748923977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347932573/10000000000 : ℝ)|^4359 ≤ (2206461595159/5000000000000 : ℝ)^3335
        have hw : |(5347932573/10000000000 : ℝ)|=(5347932573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079003309/10000000000 : ℝ)|^4359 ≤ (6417635122499/50000000000000 : ℝ)^3335
        have hw : |(-2079003309/10000000000 : ℝ)|=(2079003309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246224419/10000000000 : ℝ)|^4359 ≤ (21517748923977/50000000000000 : ℝ)^3335
        have hw : |(5246224419/10000000000 : ℝ)|=(5246224419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347932689/10000000000 : ℝ)*x 0 + (1049244873/2000000000 : ℝ)*x 1 + (-83160129/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347932689/10000000000 : ℝ)^4359 ≤ (44129233154273/100000000000000 : ℝ)^3335 := by
    have hnat : (5347932689 : ℕ)^4359*100000000000000^3335 ≤ 44129233154273^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347932689 10000000000 44129233154273 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049244873/2000000000 : ℝ)^4359 ≤ (43035497268973/100000000000000 : ℝ)^3335 := by
    have hnat : (1049244873 : ℕ)^4359*100000000000000^3335 ≤ 43035497268973^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049244873 2000000000 43035497268973 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83160129/400000000 : ℝ)^4359 ≤ (12835269567169/100000000000000 : ℝ)^3335 := by
    have hnat : (83160129 : ℕ)^4359*100000000000000^3335 ≤ 12835269567169^3335*400000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83160129 400000000 12835269567169 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347932689/10000000000 : ℝ), (1049244873/2000000000 : ℝ), (-83160129/400000000 : ℝ)] ![(44129233154273/100000000000000 : ℝ), (43035497268973/100000000000000 : ℝ), (12835269567169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347932689/10000000000 : ℝ)|^4359 ≤ (44129233154273/100000000000000 : ℝ)^3335
        have hw : |(5347932689/10000000000 : ℝ)|=(5347932689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049244873/2000000000 : ℝ)|^4359 ≤ (43035497268973/100000000000000 : ℝ)^3335
        have hw : |(1049244873/2000000000 : ℝ)|=(1049244873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83160129/400000000 : ℝ)|^4359 ≤ (12835269567169/100000000000000 : ℝ)^3335
        have hw : |(-83160129/400000000 : ℝ)|=(83160129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311934463/10000000000 : ℝ)*x 0 + (517530663/1250000000 : ℝ)*x 1 + (14031533/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311934463/10000000000 : ℝ)^4359 ≤ (6660847924507/20000000000000 : ℝ)^3335 := by
    have hnat : (4311934463 : ℕ)^4359*20000000000000^3335 ≤ 6660847924507^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311934463 10000000000 6660847924507 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517530663/1250000000 : ℝ)^4359 ≤ (31581683606651/100000000000000 : ℝ)^3335 := by
    have hnat : (517530663 : ℕ)^4359*100000000000000^3335 ≤ 31581683606651^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517530663 1250000000 31581683606651 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14031533/31250000 : ℝ)^4359 ≤ (7022815350053/20000000000000 : ℝ)^3335 := by
    have hnat : (14031533 : ℕ)^4359*20000000000000^3335 ≤ 7022815350053^3335*31250000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14031533 31250000 7022815350053 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311934463/10000000000 : ℝ), (517530663/1250000000 : ℝ), (14031533/31250000 : ℝ)] ![(6660847924507/20000000000000 : ℝ), (31581683606651/100000000000000 : ℝ), (7022815350053/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311934463/10000000000 : ℝ)|^4359 ≤ (6660847924507/20000000000000 : ℝ)^3335
        have hw : |(4311934463/10000000000 : ℝ)|=(4311934463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517530663/1250000000 : ℝ)|^4359 ≤ (31581683606651/100000000000000 : ℝ)^3335
        have hw : |(517530663/1250000000 : ℝ)|=(517530663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14031533/31250000 : ℝ)|^4359 ≤ (7022815350053/20000000000000 : ℝ)^3335
        have hw : |(14031533/31250000 : ℝ)|=(14031533/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1995747957/10000000000 : ℝ)*x 0 + (1311703099/2500000000 : ℝ)*x 1 + (5409144661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995747957/10000000000 : ℝ)^4359 ≤ (6083809640759/50000000000000 : ℝ)^3335 := by
    have hnat : (1995747957 : ℕ)^4359*50000000000000^3335 ≤ 6083809640759^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995747957 10000000000 6083809640759 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311703099/2500000000 : ℝ)^4359 ≤ (43041802176063/100000000000000 : ℝ)^3335 := by
    have hnat : (1311703099 : ℕ)^4359*100000000000000^3335 ≤ 43041802176063^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311703099 2500000000 43041802176063 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409144661/10000000000 : ℝ)^4359 ≤ (2799411158387/6250000000000 : ℝ)^3335 := by
    have hnat : (5409144661 : ℕ)^4359*6250000000000^3335 ≤ 2799411158387^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409144661 10000000000 2799411158387 6250000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1995747957/10000000000 : ℝ), (1311703099/2500000000 : ℝ), (5409144661/10000000000 : ℝ)] ![(6083809640759/50000000000000 : ℝ), (43041802176063/100000000000000 : ℝ), (2799411158387/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1995747957/10000000000 : ℝ)|^4359 ≤ (6083809640759/50000000000000 : ℝ)^3335
        have hw : |(-1995747957/10000000000 : ℝ)|=(1995747957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311703099/2500000000 : ℝ)|^4359 ≤ (43041802176063/100000000000000 : ℝ)^3335
        have hw : |(1311703099/2500000000 : ℝ)|=(1311703099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409144661/10000000000 : ℝ)|^4359 ≤ (2799411158387/6250000000000 : ℝ)^3335
        have hw : |(5409144661/10000000000 : ℝ)|=(5409144661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061110477/2000000000 : ℝ)*x 0 + (-1916082769/10000000000 : ℝ)*x 1 + (1081828961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061110477/2000000000 : ℝ)^4359 ≤ (43672706766557/100000000000000 : ℝ)^3335 := by
    have hnat : (1061110477 : ℕ)^4359*100000000000000^3335 ≤ 43672706766557^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061110477 2000000000 43672706766557 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916082769/10000000000 : ℝ)^4359 ≤ (461468525301/4000000000000 : ℝ)^3335 := by
    have hnat : (1916082769 : ℕ)^4359*4000000000000^3335 ≤ 461468525301^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916082769 10000000000 461468525301 4000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081828961/2000000000 : ℝ)^4359 ≤ (44790580092709/100000000000000 : ℝ)^3335 := by
    have hnat : (1081828961 : ℕ)^4359*100000000000000^3335 ≤ 44790580092709^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081828961 2000000000 44790580092709 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061110477/2000000000 : ℝ), (-1916082769/10000000000 : ℝ), (1081828961/2000000000 : ℝ)] ![(43672706766557/100000000000000 : ℝ), (461468525301/4000000000000 : ℝ), (44790580092709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061110477/2000000000 : ℝ)|^4359 ≤ (43672706766557/100000000000000 : ℝ)^3335
        have hw : |(1061110477/2000000000 : ℝ)|=(1061110477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916082769/10000000000 : ℝ)|^4359 ≤ (461468525301/4000000000000 : ℝ)^3335
        have hw : |(-1916082769/10000000000 : ℝ)|=(1916082769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081828961/2000000000 : ℝ)|^4359 ≤ (44790580092709/100000000000000 : ℝ)^3335
        have hw : |(1081828961/2000000000 : ℝ)|=(1081828961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326388071/2500000000 : ℝ)*x 0 + (1352286203/2500000000 : ℝ)*x 1 + (-1916082897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326388071/2500000000 : ℝ)^4359 ≤ (21836352839951/50000000000000 : ℝ)^3335 := by
    have hnat : (1326388071 : ℕ)^4359*50000000000000^3335 ≤ 21836352839951^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326388071 2500000000 21836352839951 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352286203/2500000000 : ℝ)^4359 ≤ (44790580168471/100000000000000 : ℝ)^3335 := by
    have hnat : (1352286203 : ℕ)^4359*100000000000000^3335 ≤ 44790580168471^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352286203 2500000000 44790580168471 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916082897/10000000000 : ℝ)^4359 ≤ (1442089267481/12500000000000 : ℝ)^3335 := by
    have hnat : (1916082897 : ℕ)^4359*12500000000000^3335 ≤ 1442089267481^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916082897 10000000000 1442089267481 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326388071/2500000000 : ℝ), (1352286203/2500000000 : ℝ), (-1916082897/10000000000 : ℝ)] ![(21836352839951/50000000000000 : ℝ), (44790580168471/100000000000000 : ℝ), (1442089267481/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326388071/2500000000 : ℝ)|^4359 ≤ (21836352839951/50000000000000 : ℝ)^3335
        have hw : |(1326388071/2500000000 : ℝ)|=(1326388071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352286203/2500000000 : ℝ)|^4359 ≤ (44790580168471/100000000000000 : ℝ)^3335
        have hw : |(1352286203/2500000000 : ℝ)|=(1352286203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916082897/10000000000 : ℝ)|^4359 ≤ (1442089267481/12500000000000 : ℝ)^3335
        have hw : |(-1916082897/10000000000 : ℝ)|=(1916082897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s7_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311959439/10000000000 : ℝ)*x 0 + (897766481/2000000000 : ℝ)*x 1 + (2070754893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311959439/10000000000 : ℝ)^4359 ≤ (8326122940623/25000000000000 : ℝ)^3335 := by
    have hnat : (4311959439 : ℕ)^4359*25000000000000^3335 ≤ 8326122940623^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311959439 10000000000 8326122940623 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897766481/2000000000 : ℝ)^4359 ≤ (35101216996641/100000000000000 : ℝ)^3335 := by
    have hnat : (897766481 : ℕ)^4359*100000000000000^3335 ≤ 35101216996641^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897766481 2000000000 35101216996641 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070754893/5000000000 : ℝ)^4359 ≤ (31594291230661/100000000000000 : ℝ)^3335 := by
    have hnat : (2070754893 : ℕ)^4359*100000000000000^3335 ≤ 31594291230661^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070754893 5000000000 31594291230661 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311959439/10000000000 : ℝ), (897766481/2000000000 : ℝ), (2070754893/5000000000 : ℝ)] ![(8326122940623/25000000000000 : ℝ), (35101216996641/100000000000000 : ℝ), (31594291230661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311959439/10000000000 : ℝ)|^4359 ≤ (8326122940623/25000000000000 : ℝ)^3335
        have hw : |(4311959439/10000000000 : ℝ)|=(4311959439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897766481/2000000000 : ℝ)|^4359 ≤ (35101216996641/100000000000000 : ℝ)^3335
        have hw : |(897766481/2000000000 : ℝ)|=(897766481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070754893/5000000000 : ℝ)|^4359 ≤ (31594291230661/100000000000000 : ℝ)^3335
        have hw : |(2070754893/5000000000 : ℝ)|=(2070754893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5639/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (737/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11277/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (9252714536994487/100000000000000000000 : ℝ) := by
    have hpowers : (11277/100000 : ℝ)^2179 ≤ (9252714536994487/100000000000000000000 : ℝ)^512 := by
      have hnat : (11277 : ℕ)^2179*100000000000000000000^512 ≤ 9252714536994487^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11277 100000 9252714536994487 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11277/100000 : ℝ)) (X := (9252714536994487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14741/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (28931277363966563/100000000000000000000 : ℝ) := by
    have hpowers : (14741/100000 : ℝ)^2179 ≤ (28931277363966563/100000000000000000000 : ℝ)^512 := by
      have hnat : (14741 : ℕ)^2179*100000000000000000000^512 ≤ 28931277363966563^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14741 100000 28931277363966563 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14741/100000 : ℝ)) (X := (28931277363966563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009252714536994487/50000000000000000000 : ℝ) ≤ (10000434791605181/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50009252714536994487/50000000000000000000 : ℝ)^512 ≤ (10000434791605181/10000000000000000 : ℝ)^2179 := by
      have hnat : (50009252714536994487 : ℕ)^512*10000000000000000^2179 ≤ 10000434791605181^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009252714536994487 50000000000000000000 10000434791605181 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000434791605181/10000000000000000 : ℝ)) (X := (50009252714536994487/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000763679838019221/2000000000000000000 : ℝ) ≤ (5000448539444753/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (2000763679838019221/2000000000000000000 : ℝ)^512 ≤ (5000448539444753/5000000000000000 : ℝ)^2179 := by
      have hnat : (2000763679838019221 : ℕ)^512*5000000000000000^2179 ≤ 5000448539444753^2179*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000763679838019221 2000000000000000000 5000448539444753 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000448539444753/5000000000000000 : ℝ)) (X := (2000763679838019221/2000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028931277363966563/50000000000000000000 : ℝ) ≤ (10001359366173831/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50028931277363966563/50000000000000000000 : ℝ)^512 ≤ (10001359366173831/10000000000000000 : ℝ)^2179 := by
      have hnat : (50028931277363966563 : ℕ)^512*10000000000000000^2179 ≤ 10001359366173831^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028931277363966563 50000000000000000000 10001359366173831 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001359366173831/10000000000000000 : ℝ)) (X := (50028931277363966563/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9252714536994487/100000000000000000000 : ℝ) ≤ ((17315539845354840467/17320000000000000000 : ℝ)+2*(18491491373/13856000000000 : ℝ)*(11277/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (17315539845354840467/17320000000000000000 : ℝ)+2*(18491491373/13856000000000 : ℝ)*(11277/100000 : ℝ)=(10000434791605181/10000000000000000 : ℝ) by norm_num, show 1+2*(9252714536994487/100000000000000000000 : ℝ)=(50009252714536994487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28931277363966563/100000000000000000000 : ℝ)+(9252714536994487/100000000000000000000 : ℝ) ≤ ((17315539845354840467/17320000000000000000 : ℝ)+(18491491373/13856000000000 : ℝ)*((14741/100000 : ℝ)+(11277/100000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (17315539845354840467/17320000000000000000 : ℝ)+(18491491373/13856000000000 : ℝ)*((14741/100000 : ℝ)+(11277/100000 : ℝ))=(5000448539444753/5000000000000000 : ℝ) by norm_num, show 1+(28931277363966563/100000000000000000000 : ℝ)+(9252714536994487/100000000000000000000 : ℝ)=(2000763679838019221/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28931277363966563/100000000000000000000 : ℝ) ≤ ((17315539845354840467/17320000000000000000 : ℝ)+2*(18491491373/13856000000000 : ℝ)*(14741/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (17315539845354840467/17320000000000000000 : ℝ)+2*(18491491373/13856000000000 : ℝ)*(14741/100000 : ℝ)=(10001359366173831/10000000000000000 : ℝ) by norm_num, show 1+2*(28931277363966563/100000000000000000000 : ℝ)=(50028931277363966563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17315539845354840467/17320000000000000000 : ℝ)*(X 1 0+X 2 0)+(18491491373/13856000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (17315539845354840467/17320000000000000000 : ℝ)) (alpha := (18491491373/13856000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17315539845354840467/17320000000000000000 : ℝ)*(X 0 1+X 2 1)+(18491491373/13856000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (17315539845354840467/17320000000000000000 : ℝ)) (alpha := (18491491373/13856000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17315539845354840467/17320000000000000000 : ℝ)*(X 0 2+X 1 2)+(18491491373/13856000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (17315539845354840467/17320000000000000000 : ℝ)) (alpha := (18491491373/13856000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1995736271/10000000000 : ℝ)*X 0 0+(2704867859/5000000000 : ℝ)*X 0 1+(81972257/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347932573/10000000000 : ℝ)*X 1 0+(-2079003309/10000000000 : ℝ)*X 1 1+(5246224419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347932689/10000000000 : ℝ)*X 2 0+(1049244873/2000000000 : ℝ)*X 2 1+(-83160129/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311934463/10000000000 : ℝ)*X 0 0+(517530663/1250000000 : ℝ)*X 0 1+(14031533/31250000 : ℝ)*X 0 2+(4311934463/10000000000 : ℝ)*X 1 0+(517530663/1250000000 : ℝ)*X 1 1+(14031533/31250000 : ℝ)*X 1 2+(4311934463/10000000000 : ℝ)*X 2 0+(517530663/1250000000 : ℝ)*X 2 1+(14031533/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1995747957/10000000000 : ℝ)*X 0 0+(1311703099/2500000000 : ℝ)*X 0 1+(5409144661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061110477/2000000000 : ℝ)*X 1 0+(-1916082769/10000000000 : ℝ)*X 1 1+(1081828961/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326388071/2500000000 : ℝ)*X 2 0+(1352286203/2500000000 : ℝ)*X 2 1+(-1916082897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311959439/10000000000 : ℝ)*X 0 0+(897766481/2000000000 : ℝ)*X 0 1+(2070754893/5000000000 : ℝ)*X 0 2+(4311959439/10000000000 : ℝ)*X 1 0+(897766481/2000000000 : ℝ)*X 1 1+(2070754893/5000000000 : ℝ)*X 1 2+(4311959439/10000000000 : ℝ)*X 2 0+(897766481/2000000000 : ℝ)*X 2 1+(2070754893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (190833019419700773911399871/54125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226581443/50000000000000 : ℝ)*(base19) + (502875961/100000000000000 : ℝ)*(base23) + (8871419/20000000000000 : ℝ)*(lower2) + (20602753/100000000000000 : ℝ)*(upper3) + (43915073/50000000000000 : ℝ)*(upper5) + (280444313934843/6250000000000 : ℝ)*(major0) + (280444313934843/6250000000000 : ℝ)*(major1) + (280444313934843/6250000000000 : ℝ)*(major2) + (3057896248545111/50000000000000 : ℝ)*(sp0) + (305790145667557/5000000000000 : ℝ)*(sp1) + (1223160572727613/20000000000000 : ℝ)*(sp2) + (1429205330933349/50000000000000 : ℝ)*(sp3) + (2717355951/25000000000000 : ℝ)*(sp4) + (3900008137/100000000000000 : ℝ)*(sp7) + (571682912374967/20000000000000 : ℝ)*(f.failure) + (3057901683257013/50000000000000 : ℝ)*(f.sum) + (393273201401/433000000000000000000000000 : ℝ)*base66 + (1542274422376191681/108250000000000000000000000000000 : ℝ)*base67 + (467658485834941681/108250000000000000000000000000000 : ℝ)*base69 + (1188701552216191681/108250000000000000000000000000000 : ℝ)*base71 + (415706894829/433000000000000000000000000 : ℝ)*base73 + (1255888464314941681/108250000000000000000000000000000 : ℝ)*base75 + (205193626304941681/108250000000000000000000000000000 : ℝ)*base77 + (1334669330829941681/108250000000000000000000000000000 : ℝ)*base79 + (496492698331/433000000000000000000000000 : ℝ)*base82 + (813963/400000000000000000000 : ℝ)*base89 + (813963/400000000000000000000 : ℝ)*base91 + (813963/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4124859592318125252711/1732000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302216951/50000000000000 : ℝ)*(base19) + (502651279/100000000000000 : ℝ)*(base23) + (104726079/50000000000000 : ℝ)*(lower1) + (38245599/50000000000000 : ℝ)*(upper3) + (227281/781250000000 : ℝ)*(lower4) + (95787971/100000000000000 : ℝ)*(upper5) + (2259837812279243/50000000000000 : ℝ)*(major0) + (2259837812279243/50000000000000 : ℝ)*(major1) + (2259837812279243/50000000000000 : ℝ)*(major2) + (2462866807/50000000000000 : ℝ)*(sp1) + (48126490369713/781250000000 : ℝ)*(sp4) + (1540046309288937/25000000000000 : ℝ)*(sp5) + (1232038052934397/20000000000000 : ℝ)*(sp6) + (89973762575263/3125000000000 : ℝ)*(sp7) + (89973762575263/3125000000000 : ℝ)*(f.failure) + (48126490369713/781250000000 : ℝ)*(f.sum) + (9151991849237/1732000000000000000000000000 : ℝ)*base66 + (547227111435276481/866000000000000000000000000000000 : ℝ)*base67 + (2527031750539276481/866000000000000000000000000000000 : ℝ)*base69 + (7958802766696723519/866000000000000000000000000000000 : ℝ)*base72 + (3085174405549/1732000000000000000000000000 : ℝ)*base74 + (4227175820592723519/866000000000000000000000000000000 : ℝ)*base76 + (5136766150995276481/866000000000000000000000000000000 : ℝ)*base77 + (535369253580723519/866000000000000000000000000000000 : ℝ)*base80 + (5413558969297/1732000000000000000000000000 : ℝ)*base82 + (17507/62500000000000000000 : ℝ)*base89 + (17507/62500000000000000000 : ℝ)*base91 + (17507/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1399_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1399_box_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1832876771/10000000000 : ℝ)*x 0 + (673441903/1250000000 : ℝ)*x 1 + (2693767579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1832876771/10000000000 : ℝ)^4359 ≤ (1088631591283/10000000000000 : ℝ)^3335 := by
    have hnat : (1832876771 : ℕ)^4359*10000000000000^3335 ≤ 1088631591283^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832876771 10000000000 1088631591283 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673441903/1250000000 : ℝ)^4359 ≤ (22278421197017/50000000000000 : ℝ)^3335 := by
    have hnat : (673441903 : ℕ)^4359*50000000000000^3335 ≤ 22278421197017^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673441903 1250000000 22278421197017 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693767579/5000000000 : ℝ)^4359 ≤ (44556841680591/100000000000000 : ℝ)^3335 := by
    have hnat : (2693767579 : ℕ)^4359*100000000000000^3335 ≤ 44556841680591^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693767579 5000000000 44556841680591 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1832876771/10000000000 : ℝ), (673441903/1250000000 : ℝ), (2693767579/5000000000 : ℝ)] ![(1088631591283/10000000000000 : ℝ), (22278421197017/50000000000000 : ℝ), (44556841680591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1832876771/10000000000 : ℝ)|^4359 ≤ (1088631591283/10000000000000 : ℝ)^3335
        have hw : |(-1832876771/10000000000 : ℝ)|=(1832876771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673441903/1250000000 : ℝ)|^4359 ≤ (22278421197017/50000000000000 : ℝ)^3335
        have hw : |(673441903/1250000000 : ℝ)|=(673441903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693767579/5000000000 : ℝ)|^4359 ≤ (44556841680591/100000000000000 : ℝ)^3335
        have hw : |(2693767579/5000000000 : ℝ)|=(2693767579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528581967/1000000000 : ℝ)*x 0 + (-1972492307/10000000000 : ℝ)*x 1 + (5387535241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528581967/1000000000 : ℝ)^4359 ≤ (21730262242817/50000000000000 : ℝ)^3335 := by
    have hnat : (528581967 : ℕ)^4359*50000000000000^3335 ≤ 21730262242817^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528581967 1000000000 21730262242817 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972492307/10000000000 : ℝ)^4359 ≤ (187228639427/1562500000000 : ℝ)^3335 := by
    have hnat : (1972492307 : ℕ)^4359*1562500000000^3335 ≤ 187228639427^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972492307 10000000000 187228639427 1562500000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387535241/10000000000 : ℝ)^4359 ≤ (222784212889/500000000000 : ℝ)^3335 := by
    have hnat : (5387535241 : ℕ)^4359*500000000000^3335 ≤ 222784212889^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387535241 10000000000 222784212889 500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528581967/1000000000 : ℝ), (-1972492307/10000000000 : ℝ), (5387535241/10000000000 : ℝ)] ![(21730262242817/50000000000000 : ℝ), (187228639427/1562500000000 : ℝ), (222784212889/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528581967/1000000000 : ℝ)|^4359 ≤ (21730262242817/50000000000000 : ℝ)^3335
        have hw : |(528581967/1000000000 : ℝ)|=(528581967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972492307/10000000000 : ℝ)|^4359 ≤ (187228639427/1562500000000 : ℝ)^3335
        have hw : |(-1972492307/10000000000 : ℝ)|=(1972492307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387535241/10000000000 : ℝ)|^4359 ≤ (222784212889/500000000000 : ℝ)^3335
        have hw : |(5387535241/10000000000 : ℝ)|=(5387535241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285819951/10000000000 : ℝ)*x 0 + (5387534957/10000000000 : ℝ)*x 1 + (-1972492313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285819951/10000000000 : ℝ)^4359 ≤ (43460527505447/100000000000000 : ℝ)^3335 := by
    have hnat : (5285819951 : ℕ)^4359*100000000000000^3335 ≤ 43460527505447^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285819951 10000000000 43460527505447 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387534957/10000000000 : ℝ)^4359 ≤ (44556839507833/100000000000000 : ℝ)^3335 := by
    have hnat : (5387534957 : ℕ)^4359*100000000000000^3335 ≤ 44556839507833^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387534957 10000000000 44556839507833 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972492313/10000000000 : ℝ)^4359 ≤ (11982632970969/100000000000000 : ℝ)^3335 := by
    have hnat : (1972492313 : ℕ)^4359*100000000000000^3335 ≤ 11982632970969^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972492313 10000000000 11982632970969 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285819951/10000000000 : ℝ), (5387534957/10000000000 : ℝ), (-1972492313/10000000000 : ℝ)] ![(43460527505447/100000000000000 : ℝ), (44556839507833/100000000000000 : ℝ), (11982632970969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285819951/10000000000 : ℝ)|^4359 ≤ (43460527505447/100000000000000 : ℝ)^3335
        have hw : |(5285819951/10000000000 : ℝ)|=(5285819951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387534957/10000000000 : ℝ)|^4359 ≤ (44556839507833/100000000000000 : ℝ)^3335
        have hw : |(5387534957/10000000000 : ℝ)|=(5387534957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972492313/10000000000 : ℝ)|^4359 ≤ (11982632970969/100000000000000 : ℝ)^3335
        have hw : |(-1972492313/10000000000 : ℝ)|=(1972492313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (445884591/1000000000 : ℝ)*x 0 + (4242246849/10000000000 : ℝ)*x 1 + (2121123383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445884591/1000000000 : ℝ)^4359 ≤ (4349381177137/12500000000000 : ℝ)^3335 := by
    have hnat : (445884591 : ℕ)^4359*12500000000000^3335 ≤ 4349381177137^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445884591 1000000000 4349381177137 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242246849/10000000000 : ℝ)^4359 ≤ (32602475701393/100000000000000 : ℝ)^3335 := by
    have hnat : (4242246849 : ℕ)^4359*100000000000000^3335 ≤ 32602475701393^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242246849 10000000000 32602475701393 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121123383/5000000000 : ℝ)^4359 ≤ (16301237433833/50000000000000 : ℝ)^3335 := by
    have hnat : (2121123383 : ℕ)^4359*50000000000000^3335 ≤ 16301237433833^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121123383 5000000000 16301237433833 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445884591/1000000000 : ℝ), (4242246849/10000000000 : ℝ), (2121123383/5000000000 : ℝ)] ![(4349381177137/12500000000000 : ℝ), (32602475701393/100000000000000 : ℝ), (16301237433833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445884591/1000000000 : ℝ)|^4359 ≤ (4349381177137/12500000000000 : ℝ)^3335
        have hw : |(445884591/1000000000 : ℝ)|=(445884591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242246849/10000000000 : ℝ)|^4359 ≤ (32602475701393/100000000000000 : ℝ)^3335
        have hw : |(4242246849/10000000000 : ℝ)|=(4242246849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121123383/5000000000 : ℝ)|^4359 ≤ (16301237433833/50000000000000 : ℝ)^3335
        have hw : |(2121123383/5000000000 : ℝ)|=(2121123383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080668193/5000000000 : ℝ)*x 0 + (2633024293/5000000000 : ℝ)*x 1 + (526604877/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080668193/5000000000 : ℝ)^4359 ≤ (3375912794839/25000000000000 : ℝ)^3335 := by
    have hnat : (1080668193 : ℕ)^4359*25000000000000^3335 ≤ 3375912794839^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080668193 5000000000 3375912794839 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633024293/5000000000 : ℝ)^4359 ≤ (10812043353591/25000000000000 : ℝ)^3335 := by
    have hnat : (2633024293 : ℕ)^4359*25000000000000^3335 ≤ 10812043353591^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633024293 5000000000 10812043353591 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526604877/1000000000 : ℝ)^4359 ≤ (10812043847369/25000000000000 : ℝ)^3335 := by
    have hnat : (526604877 : ℕ)^4359*25000000000000^3335 ≤ 10812043847369^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526604877 1000000000 10812043847369 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080668193/5000000000 : ℝ), (2633024293/5000000000 : ℝ), (526604877/1000000000 : ℝ)] ![(3375912794839/25000000000000 : ℝ), (10812043353591/25000000000000 : ℝ), (10812043847369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080668193/5000000000 : ℝ)|^4359 ≤ (3375912794839/25000000000000 : ℝ)^3335
        have hw : |(-1080668193/5000000000 : ℝ)|=(1080668193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633024293/5000000000 : ℝ)|^4359 ≤ (10812043353591/25000000000000 : ℝ)^3335
        have hw : |(2633024293/5000000000 : ℝ)|=(2633024293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526604877/1000000000 : ℝ)|^4359 ≤ (10812043847369/25000000000000 : ℝ)^3335
        have hw : |(526604877/1000000000 : ℝ)|=(526604877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074189357/2000000000 : ℝ)*x 0 + (-2021622717/10000000000 : ℝ)*x 1 + (5266048379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074189357/2000000000 : ℝ)^4359 ≤ (22188805239163/50000000000000 : ℝ)^3335 := by
    have hnat : (1074189357 : ℕ)^4359*50000000000000^3335 ≤ 22188805239163^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074189357 2000000000 22188805239163 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2021622717/10000000000 : ℝ)^4359 ≤ (6187109156169/50000000000000 : ℝ)^3335 := by
    have hnat : (2021622717 : ℕ)^4359*50000000000000^3335 ≤ 6187109156169^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021622717 10000000000 6187109156169 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266048379/10000000000 : ℝ)^4359 ≤ (43248171192363/100000000000000 : ℝ)^3335 := by
    have hnat : (5266048379 : ℕ)^4359*100000000000000^3335 ≤ 43248171192363^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266048379 10000000000 43248171192363 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074189357/2000000000 : ℝ), (-2021622717/10000000000 : ℝ), (5266048379/10000000000 : ℝ)] ![(22188805239163/50000000000000 : ℝ), (6187109156169/50000000000000 : ℝ), (43248171192363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074189357/2000000000 : ℝ)|^4359 ≤ (22188805239163/50000000000000 : ℝ)^3335
        have hw : |(1074189357/2000000000 : ℝ)|=(1074189357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2021622717/10000000000 : ℝ)|^4359 ≤ (6187109156169/50000000000000 : ℝ)^3335
        have hw : |(-2021622717/10000000000 : ℝ)|=(2021622717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266048379/10000000000 : ℝ)|^4359 ≤ (43248171192363/100000000000000 : ℝ)^3335
        have hw : |(5266048379/10000000000 : ℝ)|=(5266048379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685473337/5000000000 : ℝ)*x 0 + (1316512173/2500000000 : ℝ)*x 1 + (-126351403/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685473337/5000000000 : ℝ)^4359 ≤ (2218880463979/5000000000000 : ℝ)^3335 := by
    have hnat : (2685473337 : ℕ)^4359*5000000000000^3335 ≤ 2218880463979^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685473337 5000000000 2218880463979 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316512173/2500000000 : ℝ)^4359 ≤ (43248174552201/100000000000000 : ℝ)^3335 := by
    have hnat : (1316512173 : ℕ)^4359*100000000000000^3335 ≤ 43248174552201^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316512173 2500000000 43248174552201 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126351403/625000000 : ℝ)^4359 ≤ (2474843232049/20000000000000 : ℝ)^3335 := by
    have hnat : (126351403 : ℕ)^4359*20000000000000^3335 ≤ 2474843232049^3335*625000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126351403 625000000 2474843232049 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685473337/5000000000 : ℝ), (1316512173/2500000000 : ℝ), (-126351403/625000000 : ℝ)] ![(2218880463979/5000000000000 : ℝ), (43248174552201/100000000000000 : ℝ), (2474843232049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685473337/5000000000 : ℝ)|^4359 ≤ (2218880463979/5000000000000 : ℝ)^3335
        have hw : |(2685473337/5000000000 : ℝ)|=(2685473337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316512173/2500000000 : ℝ)|^4359 ≤ (43248174552201/100000000000000 : ℝ)^3335
        have hw : |(1316512173/2500000000 : ℝ)|=(1316512173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126351403/625000000 : ℝ)|^4359 ≤ (2474843232049/20000000000000 : ℝ)^3335
        have hw : |(-126351403/625000000 : ℝ)|=(126351403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164015833/10000000000 : ℝ)*x 0 + (4389610091/10000000000 : ℝ)*x 1 + (877922011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164015833/10000000000 : ℝ)^4359 ≤ (15909443584621/50000000000000 : ℝ)^3335 := by
    have hnat : (4164015833 : ℕ)^4359*50000000000000^3335 ≤ 15909443584621^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164015833 10000000000 15909443584621 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4389610091/10000000000 : ℝ)^4359 ≤ (34090556592759/100000000000000 : ℝ)^3335 := by
    have hnat : (4389610091 : ℕ)^4359*100000000000000^3335 ≤ 34090556592759^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4389610091 10000000000 34090556592759 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877922011/2000000000 : ℝ)^4359 ≤ (8522639056833/25000000000000 : ℝ)^3335 := by
    have hnat : (877922011 : ℕ)^4359*25000000000000^3335 ≤ 8522639056833^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877922011 2000000000 8522639056833 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164015833/10000000000 : ℝ), (4389610091/10000000000 : ℝ), (877922011/2000000000 : ℝ)] ![(15909443584621/50000000000000 : ℝ), (34090556592759/100000000000000 : ℝ), (8522639056833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164015833/10000000000 : ℝ)|^4359 ≤ (15909443584621/50000000000000 : ℝ)^3335
        have hw : |(4164015833/10000000000 : ℝ)|=(4164015833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4389610091/10000000000 : ℝ)|^4359 ≤ (34090556592759/100000000000000 : ℝ)^3335
        have hw : |(4389610091/10000000000 : ℝ)|=(4389610091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(877922011/2000000000 : ℝ)|^4359 ≤ (8522639056833/25000000000000 : ℝ)^3335
        have hw : |(877922011/2000000000 : ℝ)|=(877922011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_8 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-261527597/1250000000 : ℝ)*x 0 + (207286119/400000000 : ℝ)*x 1 + (5401526593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261527597/1250000000 : ℝ)^4359 ≤ (12942031129573/100000000000000 : ℝ)^3335 := by
    have hnat : (261527597 : ℕ)^4359*100000000000000^3335 ≤ 12942031129573^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261527597 1250000000 12942031129573 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207286119/400000000 : ℝ)^4359 ≤ (169399292451/400000000000 : ℝ)^3335 := by
    have hnat : (207286119 : ℕ)^4359*400000000000^3335 ≤ 169399292451^3335*400000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207286119 400000000 169399292451 400000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401526593/10000000000 : ℝ)^4359 ≤ (44708145742367/100000000000000 : ℝ)^3335 := by
    have hnat : (5401526593 : ℕ)^4359*100000000000000^3335 ≤ 44708145742367^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401526593 10000000000 44708145742367 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261527597/1250000000 : ℝ), (207286119/400000000 : ℝ), (5401526593/10000000000 : ℝ)] ![(12942031129573/100000000000000 : ℝ), (169399292451/400000000000 : ℝ), (44708145742367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261527597/1250000000 : ℝ)|^4359 ≤ (12942031129573/100000000000000 : ℝ)^3335
        have hw : |(-261527597/1250000000 : ℝ)|=(261527597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207286119/400000000 : ℝ)|^4359 ≤ (169399292451/400000000000 : ℝ)^3335
        have hw : |(207286119/400000000 : ℝ)|=(207286119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401526593/10000000000 : ℝ)|^4359 ≤ (44708145742367/100000000000000 : ℝ)^3335
        have hw : |(5401526593/10000000000 : ℝ)|=(5401526593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_9 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276011287/10000000000 : ℝ)*x 0 + (-393341201/2000000000 : ℝ)*x 1 + (2700763181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276011287/10000000000 : ℝ)^4359 ≤ (43355147135031/100000000000000 : ℝ)^3335 := by
    have hnat : (5276011287 : ℕ)^4359*100000000000000^3335 ≤ 43355147135031^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276011287 10000000000 43355147135031 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393341201/2000000000 : ℝ)^4359 ≤ (2387341920213/20000000000000 : ℝ)^3335 := by
    have hnat : (393341201 : ℕ)^4359*20000000000000^3335 ≤ 2387341920213^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393341201 2000000000 2387341920213 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700763181/5000000000 : ℝ)^4359 ≤ (698564738177/1562500000000 : ℝ)^3335 := by
    have hnat : (2700763181 : ℕ)^4359*1562500000000^3335 ≤ 698564738177^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700763181 5000000000 698564738177 1562500000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276011287/10000000000 : ℝ), (-393341201/2000000000 : ℝ), (2700763181/5000000000 : ℝ)] ![(43355147135031/100000000000000 : ℝ), (2387341920213/20000000000000 : ℝ), (698564738177/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276011287/10000000000 : ℝ)|^4359 ≤ (43355147135031/100000000000000 : ℝ)^3335
        have hw : |(5276011287/10000000000 : ℝ)|=(5276011287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393341201/2000000000 : ℝ)|^4359 ≤ (2387341920213/20000000000000 : ℝ)^3335
        have hw : |(-393341201/2000000000 : ℝ)|=(393341201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700763181/5000000000 : ℝ)|^4359 ≤ (698564738177/1562500000000 : ℝ)^3335
        have hw : |(2700763181/5000000000 : ℝ)|=(2700763181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_10 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276011287/10000000000 : ℝ)*x 0 + (5401526479/10000000000 : ℝ)*x 1 + (-983352923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276011287/10000000000 : ℝ)^4359 ≤ (43355147135031/100000000000000 : ℝ)^3335 := by
    have hnat : (5276011287 : ℕ)^4359*100000000000000^3335 ≤ 43355147135031^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276011287 10000000000 43355147135031 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401526479/10000000000 : ℝ)^4359 ≤ (1788325780363/4000000000000 : ℝ)^3335 := by
    have hnat : (5401526479 : ℕ)^4359*4000000000000^3335 ≤ 1788325780363^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401526479 10000000000 1788325780363 4000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983352923/5000000000 : ℝ)^4359 ≤ (5968354169861/50000000000000 : ℝ)^3335 := by
    have hnat : (983352923 : ℕ)^4359*50000000000000^3335 ≤ 5968354169861^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983352923 5000000000 5968354169861 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276011287/10000000000 : ℝ), (5401526479/10000000000 : ℝ), (-983352923/5000000000 : ℝ)] ![(43355147135031/100000000000000 : ℝ), (1788325780363/4000000000000 : ℝ), (5968354169861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276011287/10000000000 : ℝ)|^4359 ≤ (43355147135031/100000000000000 : ℝ)^3335
        have hw : |(5276011287/10000000000 : ℝ)|=(5276011287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401526479/10000000000 : ℝ)|^4359 ≤ (1788325780363/4000000000000 : ℝ)^3335
        have hw : |(5401526479/10000000000 : ℝ)|=(5401526479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983352923/5000000000 : ℝ)|^4359 ≤ (5968354169861/50000000000000 : ℝ)^3335
        have hw : |(-983352923/5000000000 : ℝ)|=(983352923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_11 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4492242883/10000000000 : ℝ)*x 0 + (4225261189/10000000000 : ℝ)*x 1 + (4225261061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492242883/10000000000 : ℝ)^4359 ≤ (35136078467899/100000000000000 : ℝ)^3335 := by
    have hnat : (4492242883 : ℕ)^4359*100000000000000^3335 ≤ 35136078467899^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492242883 10000000000 35136078467899 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225261189/10000000000 : ℝ)^4359 ≤ (32431961398939/100000000000000 : ℝ)^3335 := by
    have hnat : (4225261189 : ℕ)^4359*100000000000000^3335 ≤ 32431961398939^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225261189 10000000000 32431961398939 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225261061/10000000000 : ℝ)^4359 ≤ (16215980057387/50000000000000 : ℝ)^3335 := by
    have hnat : (4225261061 : ℕ)^4359*50000000000000^3335 ≤ 16215980057387^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225261061 10000000000 16215980057387 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492242883/10000000000 : ℝ), (4225261189/10000000000 : ℝ), (4225261061/10000000000 : ℝ)] ![(35136078467899/100000000000000 : ℝ), (32431961398939/100000000000000 : ℝ), (16215980057387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492242883/10000000000 : ℝ)|^4359 ≤ (35136078467899/100000000000000 : ℝ)^3335
        have hw : |(4492242883/10000000000 : ℝ)|=(4492242883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225261189/10000000000 : ℝ)|^4359 ≤ (32431961398939/100000000000000 : ℝ)^3335
        have hw : |(4225261189/10000000000 : ℝ)|=(4225261189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225261061/10000000000 : ℝ)|^4359 ≤ (16215980057387/50000000000000 : ℝ)^3335
        have hw : |(4225261061/10000000000 : ℝ)|=(4225261061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_12 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-47555607/250000000 : ℝ)*x 0 + (273467373/500000000 : ℝ)*x 1 + (2627469659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47555607/250000000 : ℝ)^4359 ≤ (5713886057517/50000000000000 : ℝ)^3335 := by
    have hnat : (47555607 : ℕ)^4359*50000000000000^3335 ≤ 5713886057517^3335*250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47555607 250000000 5713886057517 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273467373/500000000 : ℝ)^4359 ≤ (45443266091989/100000000000000 : ℝ)^3335 := by
    have hnat : (273467373 : ℕ)^4359*100000000000000^3335 ≤ 45443266091989^3335*500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273467373 500000000 45443266091989 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627469659/5000000000 : ℝ)^4359 ≤ (43128961781949/100000000000000 : ℝ)^3335 := by
    have hnat : (2627469659 : ℕ)^4359*100000000000000^3335 ≤ 43128961781949^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627469659 5000000000 43128961781949 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47555607/250000000 : ℝ), (273467373/500000000 : ℝ), (2627469659/5000000000 : ℝ)] ![(5713886057517/50000000000000 : ℝ), (45443266091989/100000000000000 : ℝ), (43128961781949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47555607/250000000 : ℝ)|^4359 ≤ (5713886057517/50000000000000 : ℝ)^3335
        have hw : |(-47555607/250000000 : ℝ)|=(47555607/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273467373/500000000 : ℝ)|^4359 ≤ (45443266091989/100000000000000 : ℝ)^3335
        have hw : |(273467373/500000000 : ℝ)|=(273467373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627469659/5000000000 : ℝ)|^4359 ≤ (43128961781949/100000000000000 : ℝ)^3335
        have hw : |(2627469659/5000000000 : ℝ)|=(2627469659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_13 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344682333/2500000000 : ℝ)*x 0 + (-1013007107/5000000000 : ℝ)*x 1 + (2627469557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344682333/2500000000 : ℝ)^4359 ≤ (2223083843587/5000000000000 : ℝ)^3335 := by
    have hnat : (1344682333 : ℕ)^4359*5000000000000^3335 ≤ 2223083843587^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344682333 2500000000 2223083843587 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013007107/5000000000 : ℝ)^4359 ≤ (3102340878169/25000000000000 : ℝ)^3335 := by
    have hnat : (1013007107 : ℕ)^4359*25000000000000^3335 ≤ 3102340878169^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013007107 5000000000 3102340878169 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627469557/5000000000 : ℝ)^4359 ≤ (43128959593571/100000000000000 : ℝ)^3335 := by
    have hnat : (2627469557 : ℕ)^4359*100000000000000^3335 ≤ 43128959593571^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627469557 5000000000 43128959593571 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344682333/2500000000 : ℝ), (-1013007107/5000000000 : ℝ), (2627469557/5000000000 : ℝ)] ![(2223083843587/5000000000000 : ℝ), (3102340878169/25000000000000 : ℝ), (43128959593571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344682333/2500000000 : ℝ)|^4359 ≤ (2223083843587/5000000000000 : ℝ)^3335
        have hw : |(1344682333/2500000000 : ℝ)|=(1344682333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1013007107/5000000000 : ℝ)|^4359 ≤ (3102340878169/25000000000000 : ℝ)^3335
        have hw : |(-1013007107/5000000000 : ℝ)|=(1013007107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627469557/5000000000 : ℝ)|^4359 ≤ (43128959593571/100000000000000 : ℝ)^3335
        have hw : |(2627469557/5000000000 : ℝ)|=(2627469557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_14 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344682343/2500000000 : ℝ)*x 0 + (1313734837/2500000000 : ℝ)*x 1 + (-253251731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344682343/2500000000 : ℝ)^4359 ≤ (44461677303913/100000000000000 : ℝ)^3335 := by
    have hnat : (1344682343 : ℕ)^4359*100000000000000^3335 ≤ 44461677303913^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344682343 2500000000 44461677303913 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313734837/2500000000 : ℝ)^4359 ≤ (4312896210377/10000000000000 : ℝ)^3335 := by
    have hnat : (1313734837 : ℕ)^4359*10000000000000^3335 ≤ 4312896210377^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313734837 2500000000 4312896210377 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253251731/1250000000 : ℝ)^4359 ≤ (6204680291299/50000000000000 : ℝ)^3335 := by
    have hnat : (253251731 : ℕ)^4359*50000000000000^3335 ≤ 6204680291299^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253251731 1250000000 6204680291299 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344682343/2500000000 : ℝ), (1313734837/2500000000 : ℝ), (-253251731/1250000000 : ℝ)] ![(44461677303913/100000000000000 : ℝ), (4312896210377/10000000000000 : ℝ), (6204680291299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344682343/2500000000 : ℝ)|^4359 ≤ (44461677303913/100000000000000 : ℝ)^3335
        have hw : |(1344682343/2500000000 : ℝ)|=(1344682343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313734837/2500000000 : ℝ)|^4359 ≤ (4312896210377/10000000000000 : ℝ)^3335
        have hw : |(1313734837/2500000000 : ℝ)|=(1313734837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253251731/1250000000 : ℝ)|^4359 ≤ (6204680291299/50000000000000 : ℝ)^3335
        have hw : |(-253251731/1250000000 : ℝ)|=(253251731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_box_15 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4136605657/10000000000 : ℝ)*x 0 + (4403075143/10000000000 : ℝ)*x 1 + (550384343/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4136605657/10000000000 : ℝ)^4359 ≤ (6309080160043/20000000000000 : ℝ)^3335 := by
    have hnat : (4136605657 : ℕ)^4359*20000000000000^3335 ≤ 6309080160043^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136605657 10000000000 6309080160043 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4403075143/10000000000 : ℝ)^4359 ≤ (2139206351239/6250000000000 : ℝ)^3335 := by
    have hnat : (4403075143 : ℕ)^4359*6250000000000^3335 ≤ 2139206351239^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403075143 10000000000 2139206351239 6250000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550384343/1250000000 : ℝ)^4359 ≤ (6845459513171/20000000000000 : ℝ)^3335 := by
    have hnat : (550384343 : ℕ)^4359*20000000000000^3335 ≤ 6845459513171^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550384343 1250000000 6845459513171 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4136605657/10000000000 : ℝ), (4403075143/10000000000 : ℝ), (550384343/1250000000 : ℝ)] ![(6309080160043/20000000000000 : ℝ), (2139206351239/6250000000000 : ℝ), (6845459513171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4136605657/10000000000 : ℝ)|^4359 ≤ (6309080160043/20000000000000 : ℝ)^3335
        have hw : |(4136605657/10000000000 : ℝ)|=(4136605657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4403075143/10000000000 : ℝ)|^4359 ≤ (2139206351239/6250000000000 : ℝ)^3335
        have hw : |(4403075143/10000000000 : ℝ)|=(4403075143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550384343/1250000000 : ℝ)|^4359 ≤ (6845459513171/20000000000000 : ℝ)^3335
        have hw : |(550384343/1250000000 : ℝ)|=(550384343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31441/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59053/100000 : ℝ) ∧ (40141/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84571/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5639/50000 : ℝ) ^ (2179/512 : ℝ) ≤ (925620694959243/10000000000000000000 : ℝ) := by
    have hpowers : (5639/50000 : ℝ)^2179 ≤ (925620694959243/10000000000000000000 : ℝ)^512 := by
      have hnat : (5639 : ℕ)^2179*10000000000000000000^512 ≤ 925620694959243^512*50000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5639 50000 925620694959243 10000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5639/50000 : ℝ)) (X := (925620694959243/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (737/5000 : ℝ) ^ (2179/512 : ℝ) ≤ (14461462783094039/50000000000000000000 : ℝ) := by
    have hpowers : (737/5000 : ℝ)^2179 ≤ (14461462783094039/50000000000000000000 : ℝ)^512 := by
      have hnat : (737 : ℕ)^2179*50000000000000000000^512 ≤ 14461462783094039^512*5000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 5000 14461462783094039 50000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/5000 : ℝ)) (X := (14461462783094039/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000925620694959243/5000000000000000000 : ℝ) ≤ (5000217477852251/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (5000925620694959243/5000000000000000000 : ℝ)^512 ≤ (5000217477852251/5000000000000000 : ℝ)^2179 := by
      have hnat : (5000925620694959243 : ℕ)^512*5000000000000000^2179 ≤ 5000217477852251^2179*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000925620694959243 5000000000000000000 5000217477852251 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000217477852251/5000000000000000 : ℝ)) (X := (5000925620694959243/5000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009544783128945127/25000000000000000000 : ℝ) ≤ (10000896964741791/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (25009544783128945127/25000000000000000000 : ℝ)^512 ≤ (10000896964741791/10000000000000000 : ℝ)^2179 := by
      have hnat : (25009544783128945127 : ℕ)^512*10000000000000000^2179 ≤ 10000896964741791^2179*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009544783128945127 25000000000000000000 10000896964741791 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000896964741791/10000000000000000 : ℝ)) (X := (25009544783128945127/25000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014461462783094039/25000000000000000000 : ℝ) ≤ (250033974344477/250000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (25014461462783094039/25000000000000000000 : ℝ)^512 ≤ (250033974344477/250000000000000 : ℝ)^2179 := by
      have hnat : (25014461462783094039 : ℕ)^512*250000000000000^2179 ≤ 250033974344477^2179*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014461462783094039 25000000000000000000 250033974344477 250000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250033974344477/250000000000000 : ℝ)) (X := (25014461462783094039/25000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(925620694959243/10000000000000000000 : ℝ) ≤ ((865277118520097381/865500000000000000 : ℝ)+2*(462009037289/346200000000000 : ℝ)*(5639/50000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (865277118520097381/865500000000000000 : ℝ)+2*(462009037289/346200000000000 : ℝ)*(5639/50000 : ℝ)=(5000217477852251/5000000000000000 : ℝ) by norm_num, show 1+2*(925620694959243/10000000000000000000 : ℝ)=(5000925620694959243/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14461462783094039/50000000000000000000 : ℝ)+(925620694959243/10000000000000000000 : ℝ) ≤ ((865277118520097381/865500000000000000 : ℝ)+(462009037289/346200000000000 : ℝ)*((737/5000 : ℝ)+(5639/50000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (865277118520097381/865500000000000000 : ℝ)+(462009037289/346200000000000 : ℝ)*((737/5000 : ℝ)+(5639/50000 : ℝ))=(10000896964741791/10000000000000000 : ℝ) by norm_num, show 1+(14461462783094039/50000000000000000000 : ℝ)+(925620694959243/10000000000000000000 : ℝ)=(25009544783128945127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14461462783094039/50000000000000000000 : ℝ) ≤ ((865277118520097381/865500000000000000 : ℝ)+2*(462009037289/346200000000000 : ℝ)*(737/5000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (865277118520097381/865500000000000000 : ℝ)+2*(462009037289/346200000000000 : ℝ)*(737/5000 : ℝ)=(250033974344477/250000000000000 : ℝ) by norm_num, show 1+2*(14461462783094039/50000000000000000000 : ℝ)=(25014461462783094039/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (865277118520097381/865500000000000000 : ℝ)*(X 1 0+X 2 0)+(462009037289/346200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (5639/50000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (865277118520097381/865500000000000000 : ℝ)) (alpha := (462009037289/346200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (865277118520097381/865500000000000000 : ℝ)*(X 0 1+X 2 1)+(462009037289/346200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (5639/50000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (865277118520097381/865500000000000000 : ℝ)) (alpha := (462009037289/346200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (865277118520097381/865500000000000000 : ℝ)*(X 0 2+X 1 2)+(462009037289/346200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (5639/50000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (865277118520097381/865500000000000000 : ℝ)) (alpha := (462009037289/346200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1832876771/10000000000 : ℝ)*X 0 0+(673441903/1250000000 : ℝ)*X 0 1+(2693767579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528581967/1000000000 : ℝ)*X 1 0+(-1972492307/10000000000 : ℝ)*X 1 1+(5387535241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285819951/10000000000 : ℝ)*X 2 0+(5387534957/10000000000 : ℝ)*X 2 1+(-1972492313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((445884591/1000000000 : ℝ)*X 0 0+(4242246849/10000000000 : ℝ)*X 0 1+(2121123383/5000000000 : ℝ)*X 0 2+(445884591/1000000000 : ℝ)*X 1 0+(4242246849/10000000000 : ℝ)*X 1 1+(2121123383/5000000000 : ℝ)*X 1 2+(445884591/1000000000 : ℝ)*X 2 0+(4242246849/10000000000 : ℝ)*X 2 1+(2121123383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080668193/5000000000 : ℝ)*X 0 0+(2633024293/5000000000 : ℝ)*X 0 1+(526604877/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1074189357/2000000000 : ℝ)*X 1 0+(-2021622717/10000000000 : ℝ)*X 1 1+(5266048379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685473337/5000000000 : ℝ)*X 2 0+(1316512173/2500000000 : ℝ)*X 2 1+(-126351403/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164015833/10000000000 : ℝ)*X 0 0+(4389610091/10000000000 : ℝ)*X 0 1+(877922011/2000000000 : ℝ)*X 0 2+(4164015833/10000000000 : ℝ)*X 1 0+(4389610091/10000000000 : ℝ)*X 1 1+(877922011/2000000000 : ℝ)*X 1 2+(4164015833/10000000000 : ℝ)*X 2 0+(4389610091/10000000000 : ℝ)*X 2 1+(877922011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-261527597/1250000000 : ℝ)*X 0 0+(207286119/400000000 : ℝ)*X 0 1+(5401526593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276011287/10000000000 : ℝ)*X 1 0+(-393341201/2000000000 : ℝ)*X 1 1+(2700763181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276011287/10000000000 : ℝ)*X 2 0+(5401526479/10000000000 : ℝ)*X 2 1+(-983352923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4492242883/10000000000 : ℝ)*X 0 0+(4225261189/10000000000 : ℝ)*X 0 1+(4225261061/10000000000 : ℝ)*X 0 2+(4492242883/10000000000 : ℝ)*X 1 0+(4225261189/10000000000 : ℝ)*X 1 1+(4225261061/10000000000 : ℝ)*X 1 2+(4492242883/10000000000 : ℝ)*X 2 0+(4225261189/10000000000 : ℝ)*X 2 1+(4225261061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-47555607/250000000 : ℝ)*X 0 0+(273467373/500000000 : ℝ)*X 0 1+(2627469659/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344682333/2500000000 : ℝ)*X 1 0+(-1013007107/5000000000 : ℝ)*X 1 1+(2627469557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344682343/2500000000 : ℝ)*X 2 0+(1313734837/2500000000 : ℝ)*X 2 1+(-253251731/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4136605657/10000000000 : ℝ)*X 0 0+(4403075143/10000000000 : ℝ)*X 0 1+(550384343/1250000000 : ℝ)*X 0 2+(4136605657/10000000000 : ℝ)*X 1 0+(4403075143/10000000000 : ℝ)*X 1 1+(550384343/1250000000 : ℝ)*X 1 2+(4136605657/10000000000 : ℝ)*X 2 0+(4403075143/10000000000 : ℝ)*X 2 1+(550384343/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31441/50000 : ℝ) ≤ (-4535182700798820608211377926839/7212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57096093/100000000000000 : ℝ)*(lower2) + (8750791/20000000000000 : ℝ)*(lower3) + (509093/100000000000000 : ℝ)*(upper5) + (1492015323778881/50000000000000 : ℝ)*(major0) + (1492015323778881/50000000000000 : ℝ)*(major1) + (1492015323778881/50000000000000 : ℝ)*(major2) + (1900367703/20000000000000 : ℝ)*(sp1) + (13940319/1562500000000 : ℝ)*(sp3) + (4088109140622221/100000000000000 : ℝ)*(sp4) + (4088100229524589/100000000000000 : ℝ)*(sp5) + (4088081993294621/100000000000000 : ℝ)*(sp6) + (237613812398723/12500000000000 : ℝ)*(sp7) + (590740883/100000000000000 : ℝ)*(sp12) + (27738068483/100000000000000 : ℝ)*(sp14) + (9504556956851/500000000000 : ℝ)*(f.failure) + (127753429105097/3125000000000 : ℝ)*(f.sum) + (16853725723093/2885000000000000000000000000 : ℝ)*base65 + (59327147534794387/14425000000000000000000000000000 : ℝ)*base67 + (48987473152755613/14425000000000000000000000000000 : ℝ)*base70 + (4118024631230613/14425000000000000000000000000000 : ℝ)*base72 + (17122460518853/2885000000000000000000000000 : ℝ)*base73 + (4836044513105613/14425000000000000000000000000000 : ℝ)*base76 + (2719330687605613/14425000000000000000000000000000 : ℝ)*base78 + (51947056009544387/14425000000000000000000000000000 : ℝ)*base79 + (11101150802637/2885000000000000000000000000 : ℝ)*base82 + (99561/10000000000000000000 : ℝ)*base90 + (99561/10000000000000000000 : ℝ)*base92 + (99561/10000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59053/100000 : ℝ) ≤ (4259396587609674028081306771827/7212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (980297/2000000000000 : ℝ)*(lower1) + (4427893/10000000000000 : ℝ)*(lower2) + (19538177/50000000000000 : ℝ)*(upper4) + (48135509/100000000000000 : ℝ)*(lower5) + (1527313930807211/50000000000000 : ℝ)*(major0) + (1527313930807211/50000000000000 : ℝ)*(major1) + (1527313930807211/50000000000000 : ℝ)*(major2) + (2071843319029017/50000000000000 : ℝ)*(sp0) + (2071838093482351/50000000000000 : ℝ)*(sp1) + (258977653726351/6250000000000 : ℝ)*(sp2) + (972941900461371/50000000000000 : ℝ)*(sp3) + (3138793/10000000000000 : ℝ)*(sp8) + (5241240631/50000000000000 : ℝ)*(sp9) + (11052456087/25000000000000 : ℝ)*(sp10) + (972941900461371/50000000000000 : ℝ)*(f.failure) + (1035921667361491/25000000000000 : ℝ)*(f.sum) + (151531629704449/8655000000000000000000000000 : ℝ)*base65 + (222553626088361891/43275000000000000000000000000000 : ℝ)*base67 + (41776082408111891/43275000000000000000000000000000 : ℝ)*base69 + (267029229080111891/43275000000000000000000000000000 : ℝ)*base71 + (31846041761209/8655000000000000000000000000 : ℝ)*base73 + (253888055061011891/43275000000000000000000000000000 : ℝ)*base75 + (587533219642661891/43275000000000000000000000000000 : ℝ)*base77 + (97317514098911891/43275000000000000000000000000000 : ℝ)*base79 + (15566315460799/8655000000000000000000000000 : ℝ)*base81 + (13433281/1000000000000000000000 : ℝ)*base90 + (13433281/1000000000000000000000 : ℝ)*base92 + (13433281/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40141/50000 : ℝ) ≤ (144762094987927375199090964303/180312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (16700049/25000000000000 : ℝ)*(upper0) + (61464103/100000000000000 : ℝ)*(upper1) + (13463283/20000000000000 : ℝ)*(upper4) + (84103042833387/2500000000000 : ℝ)*(major0) + (84103042833387/2500000000000 : ℝ)*(major1) + (84103042833387/2500000000000 : ℝ)*(major2) + (9187528229/25000000000000 : ℝ)*(sp1) + (105378605591/100000000000000 : ℝ)*(sp2) + (1582649409/20000000000000 : ℝ)*(sp3) + (351546227/5000000000000 : ℝ)*(sp4) + (4558434977955601/100000000000000 : ℝ)*(sp8) + (182336210350689/4000000000000 : ℝ)*(sp9) + (91166732605491/2000000000000 : ℝ)*(sp10) + (267879021228273/12500000000000 : ℝ)*(sp11) + (214304008307323/10000000000000 : ℝ)*(f.failure) + (4558442008880141/100000000000000 : ℝ)*(f.sum) + (1253659361231/288500000000000000000000000 : ℝ)*base65 + (665180713190649/721250000000000000000000000000 : ℝ)*base67 + (5080966407806899/721250000000000000000000000000 : ℝ)*base69 + (4551518542919399/721250000000000000000000000000 : ℝ)*base71 + (7437084503/1126953125000000000000000 : ℝ)*base73 + (5273002817180649/721250000000000000000000000000 : ℝ)*base75 + (2923465731804399/721250000000000000000000000000 : ℝ)*base77 + (4393083022926851/721250000000000000000000000000 : ℝ)*base80 + (2086927597977/577000000000000000000000000 : ℝ)*base81 + (62847/200000000000000000000 : ℝ)*base89 + (62847/200000000000000000000 : ℝ)*base91 + (62847/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84571/100000 : ℝ) ≤ (-3049768087340123693810290933191/3606250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28128197/25000000000000 : ℝ)*(lower0) + (112094297/100000000000000 : ℝ)*(lower1) + (168708753/100000000000000 : ℝ)*(lower2) + (850313438602337/25000000000000 : ℝ)*(major0) + (850313438602337/25000000000000 : ℝ)*(major1) + (850313438602337/25000000000000 : ℝ)*(major2) + (5858856569/100000000000000 : ℝ)*(sp0) + (6411899369/2500000000000 : ℝ)*(sp5) + (15917003407/25000000000000 : ℝ)*(sp6) + (502472277/800000000000 : ℝ)*(sp7) + (2331998533063371/50000000000000 : ℝ)*(sp12) + (4663746449008551/100000000000000 : ℝ)*(sp13) + (1165984814242421/25000000000000 : ℝ)*(sp14) + (2166631427832203/100000000000000 : ℝ)*(sp15) + (541673559216707/25000000000000 : ℝ)*(f.failure) + (4664002924983311/100000000000000 : ℝ)*(f.sum) + (11140007516051/8655000000000000000000000000 : ℝ)*base65 + (28438591771661897/21637500000000000000000000000000 : ℝ)*base67 + (137425866026224397/21637500000000000000000000000000 : ℝ)*base69 + (28928424785561897/21637500000000000000000000000000 : ℝ)*base71 + (23881189320367/1081875000000000000000000000 : ℝ)*base73 + (249086552700274397/21637500000000000000000000000000 : ℝ)*base75 + (72377234755211897/21637500000000000000000000000000 : ℝ)*base77 + (84366361544261897/21637500000000000000000000000000 : ℝ)*base79 + (26578844170481/8655000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1753177/500000000000000000000 : ℝ)*base90 + (1753177/500000000000000000000 : ℝ)*base92 + (1753177/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59053/100000 : ℝ) else (40141/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84571/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1399_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1399_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59053/100000 : ℝ) else (40141/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84571/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1399_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1399_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1399_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31441/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59053/100000 : ℝ) else (40141/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84571/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:59:37.34727+00:00
-- url     : https://prove2.me/submissions/f9555b68-9e57-4af2-9481-f9826010d09c

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
theorem support_rectangle_w1056_s0_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1919330963/10000000000 : ℝ)*x 0 + (759302649/1250000000 : ℝ)*x 1 + (4769500217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919330963/10000000000 : ℝ)^8249 ≤ (695466616231/6250000000000 : ℝ)^6201 := by
    have hnat : (1919330963 : ℕ)^8249*6250000000000^6201 ≤ 695466616231^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919330963 10000000000 695466616231 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (759302649/1250000000 : ℝ)^8249 ≤ (1610101433817/3125000000000 : ℝ)^6201 := by
    have hnat : (759302649 : ℕ)^8249*3125000000000^6201 ≤ 1610101433817^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759302649 1250000000 1610101433817 3125000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769500217/10000000000 : ℝ)^8249 ≤ (37349288246007/100000000000000 : ℝ)^6201 := by
    have hnat : (4769500217 : ℕ)^8249*100000000000000^6201 ≤ 37349288246007^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769500217 10000000000 37349288246007 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1919330963/10000000000 : ℝ), (759302649/1250000000 : ℝ), (4769500217/10000000000 : ℝ)] ![(695466616231/6250000000000 : ℝ), (1610101433817/3125000000000 : ℝ), (37349288246007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1919330963/10000000000 : ℝ)|^8249 ≤ (695466616231/6250000000000 : ℝ)^6201
        have hw : |(-1919330963/10000000000 : ℝ)|=(1919330963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(759302649/1250000000 : ℝ)|^8249 ≤ (1610101433817/3125000000000 : ℝ)^6201
        have hw : |(759302649/1250000000 : ℝ)|=(759302649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769500217/10000000000 : ℝ)|^8249 ≤ (37349288246007/100000000000000 : ℝ)^6201
        have hw : |(4769500217/10000000000 : ℝ)|=(4769500217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1104327061/2000000000 : ℝ)*x 0 + (-534149983/2000000000 : ℝ)*x 1 + (4769500709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104327061/2000000000 : ℝ)^8249 ≤ (9076336684829/20000000000000 : ℝ)^6201 := by
    have hnat : (1104327061 : ℕ)^8249*20000000000000^6201 ≤ 9076336684829^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104327061 2000000000 9076336684829 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534149983/2000000000 : ℝ)^8249 ≤ (17269023190011/100000000000000 : ℝ)^6201 := by
    have hnat : (534149983 : ℕ)^8249*100000000000000^6201 ≤ 17269023190011^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534149983 2000000000 17269023190011 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769500709/10000000000 : ℝ)^8249 ≤ (18674646685623/50000000000000 : ℝ)^6201 := by
    have hnat : (4769500709 : ℕ)^8249*50000000000000^6201 ≤ 18674646685623^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769500709 10000000000 18674646685623 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104327061/2000000000 : ℝ), (-534149983/2000000000 : ℝ), (4769500709/10000000000 : ℝ)] ![(9076336684829/20000000000000 : ℝ), (17269023190011/100000000000000 : ℝ), (18674646685623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104327061/2000000000 : ℝ)|^8249 ≤ (9076336684829/20000000000000 : ℝ)^6201
        have hw : |(1104327061/2000000000 : ℝ)|=(1104327061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534149983/2000000000 : ℝ)|^8249 ≤ (17269023190011/100000000000000 : ℝ)^6201
        have hw : |(-534149983/2000000000 : ℝ)|=(534149983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769500709/10000000000 : ℝ)|^8249 ≤ (18674646685623/50000000000000 : ℝ)^6201
        have hw : |(4769500709/10000000000 : ℝ)|=(4769500709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (220865421/400000000 : ℝ)*x 0 + (953900117/2000000000 : ℝ)*x 1 + (-534149957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220865421/400000000 : ℝ)^8249 ≤ (45381685829477/100000000000000 : ℝ)^6201 := by
    have hnat : (220865421 : ℕ)^8249*100000000000000^6201 ≤ 45381685829477^6201*400000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220865421 400000000 45381685829477 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953900117/2000000000 : ℝ)^8249 ≤ (37349292079519/100000000000000 : ℝ)^6201 := by
    have hnat : (953900117 : ℕ)^8249*100000000000000^6201 ≤ 37349292079519^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953900117 2000000000 37349292079519 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534149957/2000000000 : ℝ)^8249 ≤ (2158627758977/12500000000000 : ℝ)^6201 := by
    have hnat : (534149957 : ℕ)^8249*12500000000000^6201 ≤ 2158627758977^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534149957 2000000000 2158627758977 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220865421/400000000 : ℝ), (953900117/2000000000 : ℝ), (-534149957/2000000000 : ℝ)] ![(45381685829477/100000000000000 : ℝ), (37349292079519/100000000000000 : ℝ), (2158627758977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220865421/400000000 : ℝ)|^8249 ≤ (45381685829477/100000000000000 : ℝ)^6201
        have hw : |(220865421/400000000 : ℝ)|=(220865421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(953900117/2000000000 : ℝ)|^8249 ≤ (37349292079519/100000000000000 : ℝ)^6201
        have hw : |(953900117/2000000000 : ℝ)|=(953900117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534149957/2000000000 : ℝ)|^8249 ≤ (2158627758977/12500000000000 : ℝ)^6201
        have hw : |(-534149957/2000000000 : ℝ)|=(534149957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4208038369/10000000000 : ℝ)*x 0 + (156270267/500000000 : ℝ)*x 1 + (2838896447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208038369/10000000000 : ℝ)^8249 ≤ (15808648888193/50000000000000 : ℝ)^6201 := by
    have hnat : (4208038369 : ℕ)^8249*50000000000000^6201 ≤ 15808648888193^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208038369 10000000000 15808648888193 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156270267/500000000 : ℝ)^8249 ≤ (21285772581583/100000000000000 : ℝ)^6201 := by
    have hnat : (156270267 : ℕ)^8249*100000000000000^6201 ≤ 21285772581583^6201*500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156270267 500000000 21285772581583 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2838896447/5000000000 : ℝ)^8249 ≤ (47096929618973/100000000000000 : ℝ)^6201 := by
    have hnat : (2838896447 : ℕ)^8249*100000000000000^6201 ≤ 47096929618973^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838896447 5000000000 47096929618973 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208038369/10000000000 : ℝ), (156270267/500000000 : ℝ), (2838896447/5000000000 : ℝ)] ![(15808648888193/50000000000000 : ℝ), (21285772581583/100000000000000 : ℝ), (47096929618973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208038369/10000000000 : ℝ)|^8249 ≤ (15808648888193/50000000000000 : ℝ)^6201
        have hw : |(4208038369/10000000000 : ℝ)|=(4208038369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156270267/500000000 : ℝ)|^8249 ≤ (21285772581583/100000000000000 : ℝ)^6201
        have hw : |(156270267/500000000 : ℝ)|=(156270267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2838896447/5000000000 : ℝ)|^8249 ≤ (47096929618973/100000000000000 : ℝ)^6201
        have hw : |(2838896447/5000000000 : ℝ)|=(2838896447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-384946803/2000000000 : ℝ)*x 0 + (4803197741/10000000000 : ℝ)*x 1 + (6039546409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384946803/2000000000 : ℝ)^8249 ≤ (1116915537401/10000000000000 : ℝ)^6201 := by
    have hnat : (384946803 : ℕ)^8249*10000000000000^6201 ≤ 1116915537401^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384946803 2000000000 1116915537401 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4803197741/10000000000 : ℝ)^8249 ≤ (2356295587971/6250000000000 : ℝ)^6201 := by
    have hnat : (4803197741 : ℕ)^8249*6250000000000^6201 ≤ 2356295587971^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803197741 10000000000 2356295587971 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6039546409/10000000000 : ℝ)^8249 ≤ (51130115210147/100000000000000 : ℝ)^6201 := by
    have hnat : (6039546409 : ℕ)^8249*100000000000000^6201 ≤ 51130115210147^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6039546409 10000000000 51130115210147 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384946803/2000000000 : ℝ), (4803197741/10000000000 : ℝ), (6039546409/10000000000 : ℝ)] ![(1116915537401/10000000000000 : ℝ), (2356295587971/6250000000000 : ℝ), (51130115210147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384946803/2000000000 : ℝ)|^8249 ≤ (1116915537401/10000000000000 : ℝ)^6201
        have hw : |(-384946803/2000000000 : ℝ)|=(384946803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4803197741/10000000000 : ℝ)|^8249 ≤ (2356295587971/6250000000000 : ℝ)^6201
        have hw : |(4803197741/10000000000 : ℝ)|=(4803197741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6039546409/10000000000 : ℝ)|^8249 ≤ (51130115210147/100000000000000 : ℝ)^6201
        have hw : |(6039546409/10000000000 : ℝ)|=(6039546409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167514437/10000000000 : ℝ)*x 0 + (-350176713/2500000000 : ℝ)*x 1 + (6039545079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167514437/10000000000 : ℝ)^8249 ≤ (41551570449623/100000000000000 : ℝ)^6201 := by
    have hnat : (5167514437 : ℕ)^8249*100000000000000^6201 ≤ 41551570449623^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167514437 10000000000 41551570449623 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350176713/2500000000 : ℝ)^8249 ≤ (3659164657543/50000000000000 : ℝ)^6201 := by
    have hnat : (350176713 : ℕ)^8249*50000000000000^6201 ≤ 3659164657543^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350176713 2500000000 3659164657543 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6039545079/10000000000 : ℝ)^8249 ≤ (399453908061/781250000000 : ℝ)^6201 := by
    have hnat : (6039545079 : ℕ)^8249*781250000000^6201 ≤ 399453908061^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6039545079 10000000000 399453908061 781250000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167514437/10000000000 : ℝ), (-350176713/2500000000 : ℝ), (6039545079/10000000000 : ℝ)] ![(41551570449623/100000000000000 : ℝ), (3659164657543/50000000000000 : ℝ), (399453908061/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167514437/10000000000 : ℝ)|^8249 ≤ (41551570449623/100000000000000 : ℝ)^6201
        have hw : |(5167514437/10000000000 : ℝ)|=(5167514437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350176713/2500000000 : ℝ)|^8249 ≤ (3659164657543/50000000000000 : ℝ)^6201
        have hw : |(-350176713/2500000000 : ℝ)|=(350176713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6039545079/10000000000 : ℝ)|^8249 ≤ (399453908061/781250000000 : ℝ)^6201
        have hw : |(6039545079/10000000000 : ℝ)|=(6039545079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1033503159/2000000000 : ℝ)*x 0 + (754943077/1250000000 : ℝ)*x 1 + (-175088189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033503159/2000000000 : ℝ)^8249 ≤ (5193948121949/12500000000000 : ℝ)^6201 := by
    have hnat : (1033503159 : ℕ)^8249*12500000000000^6201 ≤ 5193948121949^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033503159 2000000000 5193948121949 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754943077/1250000000 : ℝ)^8249 ≤ (10226019003509/20000000000000 : ℝ)^6201 := by
    have hnat : (754943077 : ℕ)^8249*20000000000000^6201 ≤ 10226019003509^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754943077 1250000000 10226019003509 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175088189/1250000000 : ℝ)^8249 ≤ (731832000167/10000000000000 : ℝ)^6201 := by
    have hnat : (175088189 : ℕ)^8249*10000000000000^6201 ≤ 731832000167^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175088189 1250000000 731832000167 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033503159/2000000000 : ℝ), (754943077/1250000000 : ℝ), (-175088189/1250000000 : ℝ)] ![(5193948121949/12500000000000 : ℝ), (10226019003509/20000000000000 : ℝ), (731832000167/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033503159/2000000000 : ℝ)|^8249 ≤ (5193948121949/12500000000000 : ℝ)^6201
        have hw : |(1033503159/2000000000 : ℝ)|=(1033503159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(754943077/1250000000 : ℝ)|^8249 ≤ (10226019003509/20000000000000 : ℝ)^6201
        have hw : |(754943077/1250000000 : ℝ)|=(754943077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175088189/1250000000 : ℝ)|^8249 ≤ (731832000167/10000000000000 : ℝ)^6201
        have hw : |(-175088189/1250000000 : ℝ)|=(175088189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s0_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4218608167/10000000000 : ℝ)*x 0 + (5611878917/10000000000 : ℝ)*x 1 + (3193620741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4218608167/10000000000 : ℝ)^8249 ≤ (15861493574487/50000000000000 : ℝ)^6201 := by
    have hnat : (4218608167 : ℕ)^8249*50000000000000^6201 ≤ 15861493574487^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218608167 10000000000 15861493574487 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5611878917/10000000000 : ℝ)^8249 ≤ (46370999867947/100000000000000 : ℝ)^6201 := by
    have hnat : (5611878917 : ℕ)^8249*100000000000000^6201 ≤ 46370999867947^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5611878917 10000000000 46370999867947 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193620741/10000000000 : ℝ)^8249 ≤ (21906012958781/100000000000000 : ℝ)^6201 := by
    have hnat : (3193620741 : ℕ)^8249*100000000000000^6201 ≤ 21906012958781^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193620741 10000000000 21906012958781 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4218608167/10000000000 : ℝ), (5611878917/10000000000 : ℝ), (3193620741/10000000000 : ℝ)] ![(15861493574487/50000000000000 : ℝ), (46370999867947/100000000000000 : ℝ), (21906012958781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4218608167/10000000000 : ℝ)|^8249 ≤ (15861493574487/50000000000000 : ℝ)^6201
        have hw : |(4218608167/10000000000 : ℝ)|=(4218608167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5611878917/10000000000 : ℝ)|^8249 ≤ (46370999867947/100000000000000 : ℝ)^6201
        have hw : |(5611878917/10000000000 : ℝ)|=(5611878917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193620741/10000000000 : ℝ)|^8249 ≤ (21906012958781/100000000000000 : ℝ)^6201
        have hw : |(3193620741/10000000000 : ℝ)|=(3193620741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (27/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/25000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (1031/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1031 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1031*1^256 ≤ 0^256*1^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1031/256 : ℝ) ≤ (499331298519576541/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1031 ≤ (499331298519576541/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1031*20000000000000000000^256 ≤ 499331298519576541^256*5^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 499331298519576541 20000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (499331298519576541/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1031 := by
      have hnat : (1 : ℕ)^256*1^1031 ≤ 1^1031*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20499331298519576541/20000000000000000000 : ℝ) ≤ (5030709627291699/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (20499331298519576541/20000000000000000000 : ℝ)^256 ≤ (5030709627291699/5000000000000000 : ℝ)^1031 := by
      have hnat : (20499331298519576541 : ℕ)^256*5000000000000000^1031 ≤ 5030709627291699^1031*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20499331298519576541 20000000000000000000 5030709627291699 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030709627291699/5000000000000000 : ℝ)) (X := (20499331298519576541/20000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10499331298519576541/10000000000000000000 : ℝ) ≤ (2530709627291699/2500000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (10499331298519576541/10000000000000000000 : ℝ)^256 ≤ (2530709627291699/2500000000000000 : ℝ)^1031 := by
      have hnat : (10499331298519576541 : ℕ)^256*2500000000000000^1031 ≤ 2530709627291699^1031*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10499331298519576541 10000000000000000000 2530709627291699 2500000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530709627291699/2500000000000000 : ℝ)) (X := (10499331298519576541/10000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30709627291699/2000000000000000 : ℝ)*(0 : ℝ))^(1031/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(30709627291699/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(499331298519576541/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30709627291699/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (1 : ℝ)+(30709627291699/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030709627291699/5000000000000000 : ℝ) by norm_num, show 1+(499331298519576541/20000000000000000000 : ℝ)+(0 : ℝ)=(20499331298519576541/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(499331298519576541/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30709627291699/2000000000000000 : ℝ)*(2/5 : ℝ))^(1031/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(30709627291699/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530709627291699/2500000000000000 : ℝ) by norm_num, show 1+2*(499331298519576541/20000000000000000000 : ℝ)=(10499331298519576541/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30709627291699/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30709627291699/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30709627291699/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30709627291699/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30709627291699/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30709627291699/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1919330963/10000000000 : ℝ)*X 0 0+(759302649/1250000000 : ℝ)*X 0 1+(4769500217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1104327061/2000000000 : ℝ)*X 1 0+(-534149983/2000000000 : ℝ)*X 1 1+(4769500709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((220865421/400000000 : ℝ)*X 2 0+(953900117/2000000000 : ℝ)*X 2 1+(-534149957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208038369/10000000000 : ℝ)*X 0 0+(156270267/500000000 : ℝ)*X 0 1+(2838896447/5000000000 : ℝ)*X 0 2+(4208038369/10000000000 : ℝ)*X 1 0+(156270267/500000000 : ℝ)*X 1 1+(2838896447/5000000000 : ℝ)*X 1 2+(4208038369/10000000000 : ℝ)*X 2 0+(156270267/500000000 : ℝ)*X 2 1+(2838896447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-384946803/2000000000 : ℝ)*X 0 0+(4803197741/10000000000 : ℝ)*X 0 1+(6039546409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167514437/10000000000 : ℝ)*X 1 0+(-350176713/2500000000 : ℝ)*X 1 1+(6039545079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033503159/2000000000 : ℝ)*X 2 0+(754943077/1250000000 : ℝ)*X 2 1+(-175088189/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4218608167/10000000000 : ℝ)*X 0 0+(5611878917/10000000000 : ℝ)*X 0 1+(3193620741/10000000000 : ℝ)*X 0 2+(4218608167/10000000000 : ℝ)*X 1 0+(5611878917/10000000000 : ℝ)*X 1 1+(3193620741/10000000000 : ℝ)*X 1 2+(4218608167/10000000000 : ℝ)*X 2 0+(5611878917/10000000000 : ℝ)*X 2 1+(3193620741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7134777858556146218301/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1890347/25000000000000 : ℝ)*(base1) + (1343995997/100000000000000 : ℝ)*(base19) + (630838061/50000000000000 : ℝ)*(base23) + (4514129/4000000000000 : ℝ)*(base24) + (167601239/50000000000000 : ℝ)*(upper3) + (14476652849583/2500000000000 : ℝ)*(major0) + (14476652849583/2500000000000 : ℝ)*(major1) + (14476652849583/2500000000000 : ℝ)*(major2) + (191583670471737/25000000000000 : ℝ)*(sp0) + (383168247280271/50000000000000 : ℝ)*(sp1) + (766336464027193/100000000000000 : ℝ)*(sp2) + (97947892901517/25000000000000 : ℝ)*(sp3) + (3164230979/100000000000000 : ℝ)*(sp4) + (2619981897/100000000000000 : ℝ)*(sp7) + (391794199149353/100000000000000 : ℝ)*(f.failure) + (38316891927827/5000000000000 : ℝ)*(f.sum) + (1161225806517/2500000000000000000000000000 : ℝ)*base65 + (2874834108483/5000000000000000000000000000 : ℝ)*base68 + (10219281468483/5000000000000000000000000000 : ℝ)*base70 + (5508444493483/5000000000000000000000000000 : ℝ)*base72 + (31675335983/2500000000000000000000000000 : ℝ)*base74 + (4174042223483/5000000000000000000000000000 : ℝ)*base76 + (26846924568483/5000000000000000000000000000 : ℝ)*base78 + (16149771358483/5000000000000000000000000000 : ℝ)*base80 + (15138854101517/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6821663/5000000000000000000000 : ℝ)*base89 + (6821663/5000000000000000000000 : ℝ)*base91 + (6821663/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (375884664114738520838139/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17880513/20000000000000 : ℝ)*(base1) + (178219849/25000000000000 : ℝ)*(base19) + (960375257/100000000000000 : ℝ)*(base23) + (8814971/20000000000000 : ℝ)*(base45) + (19171953/25000000000000 : ℝ)*(upper3) + (200218011/100000000000000 : ℝ)*(upper5) + (611177265635187/100000000000000 : ℝ)*(major0) + (611177265635187/100000000000000 : ℝ)*(major1) + (611177265635187/100000000000000 : ℝ)*(major2) + (254918431/50000000000000 : ℝ)*(sp2) + (40441699912203/5000000000000 : ℝ)*(sp4) + (808833195962099/100000000000000 : ℝ)*(sp5) + (789875428349/97656250000 : ℝ)*(sp6) + (12922512741607/3125000000000 : ℝ)*(sp7) + (413520497133989/100000000000000 : ℝ)*(f.failure) + (161766781768299/20000000000000 : ℝ)*(f.sum) + (40529876612713/100000000000000000000000000000 : ℝ)*base65 + (87522513812713/200000000000000000000000000000 : ℝ)*base67 + (356435377387287/200000000000000000000000000000 : ℝ)*base70 + (75198846787287/200000000000000000000000000000 : ℝ)*base72 + (173815221412713/100000000000000000000000000000 : ℝ)*base73 + (917911433587287/200000000000000000000000000000 : ℝ)*base76 + (298677488187287/200000000000000000000000000000 : ℝ)*base78 + (481504571387287/200000000000000000000000000000 : ℝ)*base80 + (110343232787287/100000000000000000000000000000 : ℝ)*base82 + (26422019/5000000000000000000000 : ℝ)*base89 + (26422019/5000000000000000000000 : ℝ)*base91 + (26422019/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1056_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (27/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_s1_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065090439/5000000000 : ℝ)*x 0 + (5725128751/10000000000 : ℝ)*x 1 + (4983754919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065090439/5000000000 : ℝ)^8249 ≤ (319560479697/2500000000000 : ℝ)^6201 := by
    have hnat : (1065090439 : ℕ)^8249*2500000000000^6201 ≤ 319560479697^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065090439 5000000000 319560479697 2500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5725128751/10000000000 : ℝ)^8249 ≤ (5952496857139/12500000000000 : ℝ)^6201 := by
    have hnat : (5725128751 : ℕ)^8249*12500000000000^6201 ≤ 5952496857139^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5725128751 10000000000 5952496857139 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4983754919/10000000000 : ℝ)^8249 ≤ (39597605940479/100000000000000 : ℝ)^6201 := by
    have hnat : (4983754919 : ℕ)^8249*100000000000000^6201 ≤ 39597605940479^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983754919 10000000000 39597605940479 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065090439/5000000000 : ℝ), (5725128751/10000000000 : ℝ), (4983754919/10000000000 : ℝ)] ![(319560479697/2500000000000 : ℝ), (5952496857139/12500000000000 : ℝ), (39597605940479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065090439/5000000000 : ℝ)|^8249 ≤ (319560479697/2500000000000 : ℝ)^6201
        have hw : |(-1065090439/5000000000 : ℝ)|=(1065090439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5725128751/10000000000 : ℝ)|^8249 ≤ (5952496857139/12500000000000 : ℝ)^6201
        have hw : |(5725128751/10000000000 : ℝ)|=(5725128751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4983754919/10000000000 : ℝ)|^8249 ≤ (39597605940479/100000000000000 : ℝ)^6201
        have hw : |(4983754919/10000000000 : ℝ)|=(4983754919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711931777/5000000000 : ℝ)*x 0 + (-2532072621/10000000000 : ℝ)*x 1 + (1245938811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711931777/5000000000 : ℝ)^8249 ≤ (11078962693643/25000000000000 : ℝ)^6201 := by
    have hnat : (2711931777 : ℕ)^8249*25000000000000^6201 ≤ 11078962693643^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711931777 5000000000 11078962693643 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2532072621/10000000000 : ℝ)^8249 ≤ (1005408739173/6250000000000 : ℝ)^6201 := by
    have hnat : (2532072621 : ℕ)^8249*6250000000000^6201 ≤ 1005408739173^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532072621 10000000000 1005408739173 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245938811/2500000000 : ℝ)^8249 ≤ (19798804687773/50000000000000 : ℝ)^6201 := by
    have hnat : (1245938811 : ℕ)^8249*50000000000000^6201 ≤ 19798804687773^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245938811 2500000000 19798804687773 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711931777/5000000000 : ℝ), (-2532072621/10000000000 : ℝ), (1245938811/2500000000 : ℝ)] ![(11078962693643/25000000000000 : ℝ), (1005408739173/6250000000000 : ℝ), (19798804687773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711931777/5000000000 : ℝ)|^8249 ≤ (11078962693643/25000000000000 : ℝ)^6201
        have hw : |(2711931777/5000000000 : ℝ)|=(2711931777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2532072621/10000000000 : ℝ)|^8249 ≤ (1005408739173/6250000000000 : ℝ)^6201
        have hw : |(-2532072621/10000000000 : ℝ)|=(2532072621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1245938811/2500000000 : ℝ)|^8249 ≤ (19798804687773/50000000000000 : ℝ)^6201
        have hw : |(1245938811/2500000000 : ℝ)|=(1245938811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5423864039/10000000000 : ℝ)*x 0 + (4983754671/10000000000 : ℝ)*x 1 + (-506414543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423864039/10000000000 : ℝ)^8249 ≤ (44315856046041/100000000000000 : ℝ)^6201 := by
    have hnat : (5423864039 : ℕ)^8249*100000000000000^6201 ≤ 44315856046041^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423864039 10000000000 44315856046041 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4983754671/10000000000 : ℝ)^8249 ≤ (39597603319259/100000000000000 : ℝ)^6201 := by
    have hnat : (4983754671 : ℕ)^8249*100000000000000^6201 ≤ 39597603319259^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983754671 10000000000 39597603319259 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506414543/2000000000 : ℝ)^8249 ≤ (3217308124239/20000000000000 : ℝ)^6201 := by
    have hnat : (506414543 : ℕ)^8249*20000000000000^6201 ≤ 3217308124239^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506414543 2000000000 3217308124239 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423864039/10000000000 : ℝ), (4983754671/10000000000 : ℝ), (-506414543/2000000000 : ℝ)] ![(44315856046041/100000000000000 : ℝ), (39597603319259/100000000000000 : ℝ), (3217308124239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423864039/10000000000 : ℝ)|^8249 ≤ (44315856046041/100000000000000 : ℝ)^6201
        have hw : |(5423864039/10000000000 : ℝ)|=(5423864039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4983754671/10000000000 : ℝ)|^8249 ≤ (39597603319259/100000000000000 : ℝ)^6201
        have hw : |(4983754671/10000000000 : ℝ)|=(4983754671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506414543/2000000000 : ℝ)|^8249 ≤ (3217308124239/20000000000000 : ℝ)^6201
        have hw : |(-506414543/2000000000 : ℝ)|=(506414543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4324630071/10000000000 : ℝ)*x 0 + (915153389/2500000000 : ℝ)*x 1 + (25553589/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324630071/10000000000 : ℝ)^8249 ≤ (16393968003513/50000000000000 : ℝ)^6201 := by
    have hnat : (4324630071 : ℕ)^8249*50000000000000^6201 ≤ 16393968003513^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324630071 10000000000 16393968003513 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915153389/2500000000 : ℝ)^8249 ≤ (26266918426033/100000000000000 : ℝ)^6201 := by
    have hnat : (915153389 : ℕ)^8249*100000000000000^6201 ≤ 26266918426033^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915153389 2500000000 26266918426033 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25553589/50000000 : ℝ)^8249 ≤ (40945145548863/100000000000000 : ℝ)^6201 := by
    have hnat : (25553589 : ℕ)^8249*100000000000000^6201 ≤ 40945145548863^6201*50000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25553589 50000000 40945145548863 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324630071/10000000000 : ℝ), (915153389/2500000000 : ℝ), (25553589/50000000 : ℝ)] ![(16393968003513/50000000000000 : ℝ), (26266918426033/100000000000000 : ℝ), (40945145548863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324630071/10000000000 : ℝ)|^8249 ≤ (16393968003513/50000000000000 : ℝ)^6201
        have hw : |(4324630071/10000000000 : ℝ)|=(4324630071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915153389/2500000000 : ℝ)|^8249 ≤ (26266918426033/100000000000000 : ℝ)^6201
        have hw : |(915153389/2500000000 : ℝ)|=(915153389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25553589/50000000 : ℝ)|^8249 ≤ (40945145548863/100000000000000 : ℝ)^6201
        have hw : |(25553589/50000000 : ℝ)|=(25553589/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065559367/5000000000 : ℝ)*x 0 + (2497106433/5000000000 : ℝ)*x 1 + (2857227803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065559367/5000000000 : ℝ)^8249 ≤ (799369132481/6250000000000 : ℝ)^6201 := by
    have hnat : (1065559367 : ℕ)^8249*6250000000000^6201 ≤ 799369132481^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065559367 5000000000 799369132481 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2497106433/5000000000 : ℝ)^8249 ≤ (9927044707319/25000000000000 : ℝ)^6201 := by
    have hnat : (2497106433 : ℕ)^8249*25000000000000^6201 ≤ 9927044707319^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497106433 5000000000 9927044707319 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2857227803/5000000000 : ℝ)^8249 ≤ (47501915038951/100000000000000 : ℝ)^6201 := by
    have hnat : (2857227803 : ℕ)^8249*100000000000000^6201 ≤ 47501915038951^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857227803 5000000000 47501915038951 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065559367/5000000000 : ℝ), (2497106433/5000000000 : ℝ), (2857227803/5000000000 : ℝ)] ![(799369132481/6250000000000 : ℝ), (9927044707319/25000000000000 : ℝ), (47501915038951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065559367/5000000000 : ℝ)|^8249 ≤ (799369132481/6250000000000 : ℝ)^6201
        have hw : |(-1065559367/5000000000 : ℝ)|=(1065559367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2497106433/5000000000 : ℝ)|^8249 ≤ (9927044707319/25000000000000 : ℝ)^6201
        have hw : |(2497106433/5000000000 : ℝ)|=(2497106433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2857227803/5000000000 : ℝ)|^8249 ≤ (47501915038951/100000000000000 : ℝ)^6201
        have hw : |(2857227803/5000000000 : ℝ)|=(2857227803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617313993/5000000000 : ℝ)*x 0 + (-1801370341/10000000000 : ℝ)*x 1 + (5714457073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617313993/5000000000 : ℝ)^8249 ≤ (42270991722481/100000000000000 : ℝ)^6201 := by
    have hnat : (2617313993 : ℕ)^8249*100000000000000^6201 ≤ 42270991722481^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617313993 5000000000 42270991722481 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1801370341/10000000000 : ℝ)^8249 ≤ (639192312779/6250000000000 : ℝ)^6201 := by
    have hnat : (1801370341 : ℕ)^8249*6250000000000^6201 ≤ 639192312779^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801370341 10000000000 639192312779 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5714457073/10000000000 : ℝ)^8249 ≤ (47501931261009/100000000000000 : ℝ)^6201 := by
    have hnat : (5714457073 : ℕ)^8249*100000000000000^6201 ≤ 47501931261009^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714457073 10000000000 47501931261009 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617313993/5000000000 : ℝ), (-1801370341/10000000000 : ℝ), (5714457073/10000000000 : ℝ)] ![(42270991722481/100000000000000 : ℝ), (639192312779/6250000000000 : ℝ), (47501931261009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617313993/5000000000 : ℝ)|^8249 ≤ (42270991722481/100000000000000 : ℝ)^6201
        have hw : |(2617313993/5000000000 : ℝ)|=(2617313993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1801370341/10000000000 : ℝ)|^8249 ≤ (639192312779/6250000000000 : ℝ)^6201
        have hw : |(-1801370341/10000000000 : ℝ)|=(1801370341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5714457073/10000000000 : ℝ)|^8249 ≤ (47501931261009/100000000000000 : ℝ)^6201
        have hw : |(5714457073/10000000000 : ℝ)|=(5714457073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5234626011/10000000000 : ℝ)*x 0 + (1142891849/2000000000 : ℝ)*x 1 + (-1801369969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234626011/10000000000 : ℝ)^8249 ≤ (42270970506493/100000000000000 : ℝ)^6201 := by
    have hnat : (5234626011 : ℕ)^8249*100000000000000^6201 ≤ 42270970506493^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234626011 10000000000 42270970506493 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142891849/2000000000 : ℝ)^8249 ≤ (47501955278947/100000000000000 : ℝ)^6201 := by
    have hnat : (1142891849 : ℕ)^8249*100000000000000^6201 ≤ 47501955278947^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142891849 2000000000 47501955278947 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1801369969/10000000000 : ℝ)^8249 ≤ (10227074194951/100000000000000 : ℝ)^6201 := by
    have hnat : (1801369969 : ℕ)^8249*100000000000000^6201 ≤ 10227074194951^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801369969 10000000000 10227074194951 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234626011/10000000000 : ℝ), (1142891849/2000000000 : ℝ), (-1801369969/10000000000 : ℝ)] ![(42270970506493/100000000000000 : ℝ), (47501955278947/100000000000000 : ℝ), (10227074194951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234626011/10000000000 : ℝ)|^8249 ≤ (42270970506493/100000000000000 : ℝ)^6201
        have hw : |(5234626011/10000000000 : ℝ)|=(5234626011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142891849/2000000000 : ℝ)|^8249 ≤ (47501955278947/100000000000000 : ℝ)^6201
        have hw : |(1142891849/2000000000 : ℝ)|=(1142891849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1801369969/10000000000 : ℝ)|^8249 ≤ (10227074194951/100000000000000 : ℝ)^6201
        have hw : |(-1801369969/10000000000 : ℝ)|=(1801369969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s1_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4326460927/10000000000 : ℝ)*x 0 + (5090258941/10000000000 : ℝ)*x 1 + (184074343/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326460927/10000000000 : ℝ)^8249 ≤ (4100800338053/12500000000000 : ℝ)^6201 := by
    have hnat : (4326460927 : ℕ)^8249*12500000000000^6201 ≤ 4100800338053^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326460927 10000000000 4100800338053 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5090258941/10000000000 : ℝ)^8249 ≤ (20363623570999/50000000000000 : ℝ)^6201 := by
    have hnat : (5090258941 : ℕ)^8249*50000000000000^6201 ≤ 20363623570999^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090258941 10000000000 20363623570999 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184074343/500000000 : ℝ)^8249 ≤ (1654146884309/6250000000000 : ℝ)^6201 := by
    have hnat : (184074343 : ℕ)^8249*6250000000000^6201 ≤ 1654146884309^6201*500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184074343 500000000 1654146884309 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326460927/10000000000 : ℝ), (5090258941/10000000000 : ℝ), (184074343/500000000 : ℝ)] ![(4100800338053/12500000000000 : ℝ), (20363623570999/50000000000000 : ℝ), (1654146884309/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326460927/10000000000 : ℝ)|^8249 ≤ (4100800338053/12500000000000 : ℝ)^6201
        have hw : |(4326460927/10000000000 : ℝ)|=(4326460927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5090258941/10000000000 : ℝ)|^8249 ≤ (20363623570999/50000000000000 : ℝ)^6201
        have hw : |(5090258941/10000000000 : ℝ)|=(5090258941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184074343/500000000 : ℝ)|^8249 ≤ (1654146884309/6250000000000 : ℝ)^6201
        have hw : |(184074343/500000000 : ℝ)|=(184074343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20839/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (27/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (27/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (27/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (27/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (27/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (27/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (27/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (3460959/50000000000000000000 : ℝ) := by
    have hpowers : (27/50000 : ℝ)^1031 ≤ (3460959/50000000000000000000 : ℝ)^256 := by
      have hnat : (27 : ℕ)^1031*50000000000000000000^256 ≤ 3460959^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27 50000 3460959 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27/50000 : ℝ)) (X := (3460959/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/25000 : ℝ) ^ (1031/256 : ℝ) ≤ (606367618209670647/100000000000000000000 : ℝ) := by
    have hpowers : (7037/25000 : ℝ)^1031 ≤ (606367618209670647/100000000000000000000 : ℝ)^256 := by
      have hnat : (7037 : ℕ)^1031*100000000000000000000^256 ≤ 606367618209670647^256*25000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 25000 606367618209670647 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/25000 : ℝ)) (X := (606367618209670647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000003460959/25000000000000000000 : ℝ) ≤ (1250000000000043/1250000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25000000000003460959/25000000000000000000 : ℝ)^256 ≤ (1250000000000043/1250000000000000 : ℝ)^1031 := by
      have hnat : (25000000000003460959 : ℕ)^256*1250000000000000^1031 ≤ 1250000000000043^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000003460959 25000000000000000000 1250000000000043 1250000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000000043/1250000000000000 : ℝ)) (X := (25000000000003460959/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20121273523643318513/20000000000000000000 : ℝ) ≤ (2503755518534417/2500000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (20121273523643318513/20000000000000000000 : ℝ)^256 ≤ (2503755518534417/2500000000000000 : ℝ)^1031 := by
      have hnat : (20121273523643318513 : ℕ)^256*2500000000000000^1031 ≤ 2503755518534417^1031*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20121273523643318513 20000000000000000000 2503755518534417 2500000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503755518534417/2500000000000000 : ℝ)) (X := (20121273523643318513/20000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50606367618209670647/50000000000000000000 : ℝ) ≤ (626877759267187/625000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50606367618209670647/50000000000000000000 : ℝ)^256 ≤ (626877759267187/625000000000000 : ℝ)^1031 := by
      have hnat : (50606367618209670647 : ℕ)^256*625000000000000^1031 ≤ 626877759267187^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50606367618209670647 50000000000000000000 626877759267187 625000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626877759267187/625000000000000 : ℝ)) (X := (50606367618209670647/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3460959/50000000000000000000 : ℝ) ≤ ((4389662150250044271/4389687500000000000 : ℝ)+2*(3755518534331/702350000000000 : ℝ)*(27/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (4389662150250044271/4389687500000000000 : ℝ)+2*(3755518534331/702350000000000 : ℝ)*(27/50000 : ℝ)=(1250000000000043/1250000000000000 : ℝ) by norm_num, show 1+2*(3460959/50000000000000000000 : ℝ)=(25000000000003460959/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(606367618209670647/100000000000000000000 : ℝ)+(3460959/50000000000000000000 : ℝ) ≤ ((4389662150250044271/4389687500000000000 : ℝ)+(3755518534331/702350000000000 : ℝ)*((7037/25000 : ℝ)+(27/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (4389662150250044271/4389687500000000000 : ℝ)+(3755518534331/702350000000000 : ℝ)*((7037/25000 : ℝ)+(27/50000 : ℝ))=(2503755518534417/2500000000000000 : ℝ) by norm_num, show 1+(606367618209670647/100000000000000000000 : ℝ)+(3460959/50000000000000000000 : ℝ)=(20121273523643318513/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(606367618209670647/100000000000000000000 : ℝ) ≤ ((4389662150250044271/4389687500000000000 : ℝ)+2*(3755518534331/702350000000000 : ℝ)*(7037/25000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (4389662150250044271/4389687500000000000 : ℝ)+2*(3755518534331/702350000000000 : ℝ)*(7037/25000 : ℝ)=(626877759267187/625000000000000 : ℝ) by norm_num, show 1+2*(606367618209670647/100000000000000000000 : ℝ)=(50606367618209670647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4389662150250044271/4389687500000000000 : ℝ)*(X 1 0+X 2 0)+(3755518534331/702350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (27/50000 : ℝ)) (hi := (7037/25000 : ℝ)) (c := (4389662150250044271/4389687500000000000 : ℝ)) (alpha := (3755518534331/702350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4389662150250044271/4389687500000000000 : ℝ)*(X 0 1+X 2 1)+(3755518534331/702350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (27/50000 : ℝ)) (hi := (7037/25000 : ℝ)) (c := (4389662150250044271/4389687500000000000 : ℝ)) (alpha := (3755518534331/702350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4389662150250044271/4389687500000000000 : ℝ)*(X 0 2+X 1 2)+(3755518534331/702350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (27/50000 : ℝ)) (hi := (7037/25000 : ℝ)) (c := (4389662150250044271/4389687500000000000 : ℝ)) (alpha := (3755518534331/702350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1065090439/5000000000 : ℝ)*X 0 0+(5725128751/10000000000 : ℝ)*X 0 1+(4983754919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711931777/5000000000 : ℝ)*X 1 0+(-2532072621/10000000000 : ℝ)*X 1 1+(1245938811/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5423864039/10000000000 : ℝ)*X 2 0+(4983754671/10000000000 : ℝ)*X 2 1+(-506414543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324630071/10000000000 : ℝ)*X 0 0+(915153389/2500000000 : ℝ)*X 0 1+(25553589/50000000 : ℝ)*X 0 2+(4324630071/10000000000 : ℝ)*X 1 0+(915153389/2500000000 : ℝ)*X 1 1+(25553589/50000000 : ℝ)*X 1 2+(4324630071/10000000000 : ℝ)*X 2 0+(915153389/2500000000 : ℝ)*X 2 1+(25553589/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065559367/5000000000 : ℝ)*X 0 0+(2497106433/5000000000 : ℝ)*X 0 1+(2857227803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617313993/5000000000 : ℝ)*X 1 0+(-1801370341/10000000000 : ℝ)*X 1 1+(5714457073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5234626011/10000000000 : ℝ)*X 2 0+(1142891849/2000000000 : ℝ)*X 2 1+(-1801369969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326460927/10000000000 : ℝ)*X 0 0+(5090258941/10000000000 : ℝ)*X 0 1+(184074343/500000000 : ℝ)*X 0 2+(4326460927/10000000000 : ℝ)*X 1 0+(5090258941/10000000000 : ℝ)*X 1 1+(184074343/500000000 : ℝ)*X 1 2+(4326460927/10000000000 : ℝ)*X 2 0+(5090258941/10000000000 : ℝ)*X 2 1+(184074343/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1410858834725844966669979569/219484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22555819/20000000000000 : ℝ)*(base1) + (5677319/400000000000 : ℝ)*(base19) + (48123261/3125000000000 : ℝ)*(base23) + (150875987/100000000000000 : ℝ)*(upper3) + (76185893/50000000000000 : ℝ)*(upper5) + (509618570778847/50000000000000 : ℝ)*(major0) + (509618570778847/50000000000000 : ℝ)*(major1) + (509618570778847/50000000000000 : ℝ)*(major2) + (168606778176799/12500000000000 : ℝ)*(sp0) + (1348860202895049/100000000000000 : ℝ)*(sp1) + (658623087051/48828125000 : ℝ)*(sp2) + (172402214616341/25000000000000 : ℝ)*(sp3) + (7509589503/100000000000000 : ℝ)*(sp4) + (21721109/625000000000 : ℝ)*(sp7) + (344806223310949/50000000000000 : ℝ)*(f.failure) + (1686077027781/125000000000 : ℝ)*(f.sum) + (31910354692941/35117500000000000000000000000 : ℝ)*base66 + (609376582579589463/219484375000000000000000000000000 : ℝ)*base68 + (2049176579139651963/219484375000000000000000000000000 : ℝ)*base70 + (94750790664464463/219484375000000000000000000000000 : ℝ)*base72 + (258302102083397/70235000000000000000000000000 : ℝ)*base74 + (296038354644254287/219484375000000000000000000000000 : ℝ)*base75 + (415607388075745713/219484375000000000000000000000000 : ℝ)*base78 + (1105947386564683213/219484375000000000000000000000000 : ℝ)*base80 + (106799565853843/17558750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12581821/2500000000000000000000 : ℝ)*base90 + (12581821/2500000000000000000000 : ℝ)*base92 + (12581821/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (456134125962501105695960301/109742187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2672654331/100000000000000 : ℝ)*(base19) + (1277473319/50000000000000 : ℝ)*(base23) + (195367973/100000000000000 : ℝ)*(upper2) + (403658461/100000000000000 : ℝ)*(upper3) + (533846133/100000000000000 : ℝ)*(upper5) + (262282129006713/25000000000000 : ℝ)*(major0) + (262282129006713/25000000000000 : ℝ)*(major1) + (262282129006713/25000000000000 : ℝ)*(major2) + (12938249343/100000000000000 : ℝ)*(sp1) + (6924257809/50000000000000 : ℝ)*(sp2) + (694210021364849/50000000000000 : ℝ)*(sp4) + (173550553978253/12500000000000 : ℝ)*(sp5) + (1388403639267441/100000000000000 : ℝ)*(sp6) + (354918425388409/50000000000000 : ℝ)*(sp7) + (354918425388409/50000000000000 : ℝ)*(f.failure) + (694210021364849/50000000000000 : ℝ)*(f.sum) + (130696211181417/35117500000000000000000000000 : ℝ)*base65 + (194731030229857663/27435546875000000000000000000000 : ℝ)*base68 + (961235992468758777/109742187500000000000000000000000 : ℝ)*base70 + (706639001435071277/109742187500000000000000000000000 : ℝ)*base72 + (206689409182461/70235000000000000000000000000 : ℝ)*base74 + (766913904972133777/109742187500000000000000000000000 : ℝ)*base76 + (64199445527529321/219484375000000000000000000000000 : ℝ)*base77 + (100910797073001929/219484375000000000000000000000000 : ℝ)*base80 + (196900878739011/70235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16949839/2500000000000000000000 : ℝ)*base89 + (16949839/2500000000000000000000 : ℝ)*base91 + (16949839/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1056_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20839/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_s2_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188164653/10000000000 : ℝ)*x 0 + (5527991617/10000000000 : ℝ)*x 1 + (5144115407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188164653/10000000000 : ℝ)^8249 ≤ (165591746523/1250000000000 : ℝ)^6201 := by
    have hnat : (2188164653 : ℕ)^8249*1250000000000^6201 ≤ 165591746523^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188164653 10000000000 165591746523 1250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527991617/10000000000 : ℝ)^8249 ≤ (11362798072041/25000000000000 : ℝ)^6201 := by
    have hnat : (5527991617 : ℕ)^8249*25000000000000^6201 ≤ 11362798072041^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527991617 10000000000 11362798072041 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144115407/10000000000 : ℝ)^8249 ≤ (10325366995349/25000000000000 : ℝ)^6201 := by
    have hnat : (5144115407 : ℕ)^8249*25000000000000^6201 ≤ 10325366995349^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144115407 10000000000 10325366995349 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188164653/10000000000 : ℝ), (5527991617/10000000000 : ℝ), (5144115407/10000000000 : ℝ)] ![(165591746523/1250000000000 : ℝ), (11362798072041/25000000000000 : ℝ), (10325366995349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188164653/10000000000 : ℝ)|^8249 ≤ (165591746523/1250000000000 : ℝ)^6201
        have hw : |(-2188164653/10000000000 : ℝ)|=(2188164653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527991617/10000000000 : ℝ)|^8249 ≤ (11362798072041/25000000000000 : ℝ)^6201
        have hw : |(5527991617/10000000000 : ℝ)|=(5527991617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144115407/10000000000 : ℝ)|^8249 ≤ (10325366995349/25000000000000 : ℝ)^6201
        have hw : |(5144115407/10000000000 : ℝ)|=(5144115407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075530789/2000000000 : ℝ)*x 0 + (-2388445093/10000000000 : ℝ)*x 1 + (3215073/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075530789/2000000000 : ℝ)^8249 ≤ (21907153065401/50000000000000 : ℝ)^6201 := by
    have hnat : (1075530789 : ℕ)^8249*50000000000000^6201 ≤ 21907153065401^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075530789 2000000000 21907153065401 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2388445093/10000000000 : ℝ)^8249 ≤ (1488421098977/10000000000000 : ℝ)^6201 := by
    have hnat : (2388445093 : ℕ)^8249*10000000000000^6201 ≤ 1488421098977^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388445093 10000000000 1488421098977 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3215073/6250000 : ℝ)^8249 ≤ (10325370714857/25000000000000 : ℝ)^6201 := by
    have hnat : (3215073 : ℕ)^8249*25000000000000^6201 ≤ 10325370714857^6201*6250000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3215073 6250000 10325370714857 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075530789/2000000000 : ℝ), (-2388445093/10000000000 : ℝ), (3215073/6250000 : ℝ)] ![(21907153065401/50000000000000 : ℝ), (1488421098977/10000000000000 : ℝ), (10325370714857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075530789/2000000000 : ℝ)|^8249 ≤ (21907153065401/50000000000000 : ℝ)^6201
        have hw : |(1075530789/2000000000 : ℝ)|=(1075530789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2388445093/10000000000 : ℝ)|^8249 ≤ (1488421098977/10000000000000 : ℝ)^6201
        have hw : |(-2388445093/10000000000 : ℝ)|=(2388445093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3215073/6250000 : ℝ)|^8249 ≤ (10325370714857/25000000000000 : ℝ)^6201
        have hw : |(3215073/6250000 : ℝ)|=(3215073/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (672206767/1250000000 : ℝ)*x 0 + (5144116397/10000000000 : ℝ)*x 1 + (-597111341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672206767/1250000000 : ℝ)^8249 ≤ (1752572328037/4000000000000 : ℝ)^6201 := by
    have hnat : (672206767 : ℕ)^8249*4000000000000^6201 ≤ 1752572328037^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672206767 1250000000 1752572328037 4000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144116397/10000000000 : ℝ)^8249 ≤ (41301478555159/100000000000000 : ℝ)^6201 := by
    have hnat : (5144116397 : ℕ)^8249*100000000000000^6201 ≤ 41301478555159^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144116397 10000000000 41301478555159 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597111341/2500000000 : ℝ)^8249 ≤ (7442106618169/50000000000000 : ℝ)^6201 := by
    have hnat : (597111341 : ℕ)^8249*50000000000000^6201 ≤ 7442106618169^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597111341 2500000000 7442106618169 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672206767/1250000000 : ℝ), (5144116397/10000000000 : ℝ), (-597111341/2500000000 : ℝ)] ![(1752572328037/4000000000000 : ℝ), (41301478555159/100000000000000 : ℝ), (7442106618169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672206767/1250000000 : ℝ)|^8249 ≤ (1752572328037/4000000000000 : ℝ)^6201
        have hw : |(672206767/1250000000 : ℝ)|=(672206767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144116397/10000000000 : ℝ)|^8249 ≤ (41301478555159/100000000000000 : ℝ)^6201
        have hw : |(5144116397/10000000000 : ℝ)|=(5144116397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-597111341/2500000000 : ℝ)|^8249 ≤ (7442106618169/50000000000000 : ℝ)^6201
        have hw : |(-597111341/2500000000 : ℝ)|=(597111341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364167757/10000000000 : ℝ)*x 0 + (4005065753/10000000000 : ℝ)*x 1 + (297244381/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364167757/10000000000 : ℝ)^8249 ≤ (33187300802797/100000000000000 : ℝ)^6201 := by
    have hnat : (4364167757 : ℕ)^8249*100000000000000^6201 ≤ 33187300802797^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364167757 10000000000 33187300802797 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4005065753/10000000000 : ℝ)^8249 ≤ (14802457326267/50000000000000 : ℝ)^6201 := by
    have hnat : (4005065753 : ℕ)^8249*50000000000000^6201 ≤ 14802457326267^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005065753 10000000000 14802457326267 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297244381/625000000 : ℝ)^8249 ≤ (37207784536379/100000000000000 : ℝ)^6201 := by
    have hnat : (297244381 : ℕ)^8249*100000000000000^6201 ≤ 37207784536379^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297244381 625000000 37207784536379 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364167757/10000000000 : ℝ), (4005065753/10000000000 : ℝ), (297244381/625000000 : ℝ)] ![(33187300802797/100000000000000 : ℝ), (14802457326267/50000000000000 : ℝ), (37207784536379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364167757/10000000000 : ℝ)|^8249 ≤ (33187300802797/100000000000000 : ℝ)^6201
        have hw : |(4364167757/10000000000 : ℝ)|=(4364167757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4005065753/10000000000 : ℝ)|^8249 ≤ (14802457326267/50000000000000 : ℝ)^6201
        have hw : |(4005065753/10000000000 : ℝ)|=(4005065753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297244381/625000000 : ℝ)|^8249 ≤ (37207784536379/100000000000000 : ℝ)^6201
        have hw : |(297244381/625000000 : ℝ)|=(297244381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188293787/10000000000 : ℝ)*x 0 + (128673221/250000000 : ℝ)*x 1 + (2762574347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188293787/10000000000 : ℝ)^8249 ≤ (3312094930307/25000000000000 : ℝ)^6201 := by
    have hnat : (2188293787 : ℕ)^8249*25000000000000^6201 ≤ 3312094930307^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188293787 10000000000 3312094930307 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128673221/250000000 : ℝ)^8249 ≤ (41331519757971/100000000000000 : ℝ)^6201 := by
    have hnat : (128673221 : ℕ)^8249*100000000000000^6201 ≤ 41331519757971^6201*250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128673221 250000000 41331519757971 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762574347/5000000000 : ℝ)^8249 ≤ (11355025125261/25000000000000 : ℝ)^6201 := by
    have hnat : (2762574347 : ℕ)^8249*25000000000000^6201 ≤ 11355025125261^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762574347 5000000000 11355025125261 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188293787/10000000000 : ℝ), (128673221/250000000 : ℝ), (2762574347/5000000000 : ℝ)] ![(3312094930307/25000000000000 : ℝ), (41331519757971/100000000000000 : ℝ), (11355025125261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188293787/10000000000 : ℝ)|^8249 ≤ (3312094930307/25000000000000 : ℝ)^6201
        have hw : |(-2188293787/10000000000 : ℝ)|=(2188293787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128673221/250000000 : ℝ)|^8249 ≤ (41331519757971/100000000000000 : ℝ)^6201
        have hw : |(128673221/250000000 : ℝ)|=(128673221/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762574347/5000000000 : ℝ)|^8249 ≤ (11355025125261/25000000000000 : ℝ)^6201
        have hw : |(2762574347/5000000000 : ℝ)|=(2762574347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320207089/2500000000 : ℝ)*x 0 + (-1003706979/5000000000 : ℝ)*x 1 + (5525148769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320207089/2500000000 : ℝ)^8249 ≤ (8553602125257/20000000000000 : ℝ)^6201 := by
    have hnat : (1320207089 : ℕ)^8249*20000000000000^6201 ≤ 8553602125257^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320207089 2500000000 8553602125257 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003706979/5000000000 : ℝ)^8249 ≤ (5905944019891/50000000000000 : ℝ)^6201 := by
    have hnat : (1003706979 : ℕ)^8249*50000000000000^6201 ≤ 5905944019891^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003706979 5000000000 5905944019891 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5525148769/10000000000 : ℝ)^8249 ≤ (88711135393/195312500000 : ℝ)^6201 := by
    have hnat : (5525148769 : ℕ)^8249*195312500000^6201 ≤ 88711135393^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525148769 10000000000 88711135393 195312500000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320207089/2500000000 : ℝ), (-1003706979/5000000000 : ℝ), (5525148769/10000000000 : ℝ)] ![(8553602125257/20000000000000 : ℝ), (5905944019891/50000000000000 : ℝ), (88711135393/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320207089/2500000000 : ℝ)|^8249 ≤ (8553602125257/20000000000000 : ℝ)^6201
        have hw : |(1320207089/2500000000 : ℝ)|=(1320207089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1003706979/5000000000 : ℝ)|^8249 ≤ (5905944019891/50000000000000 : ℝ)^6201
        have hw : |(-1003706979/5000000000 : ℝ)|=(1003706979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5525148769/10000000000 : ℝ)|^8249 ≤ (88711135393/195312500000 : ℝ)^6201
        have hw : |(5525148769/10000000000 : ℝ)|=(5525148769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056165719/2000000000 : ℝ)*x 0 + (1105029721/2000000000 : ℝ)*x 1 + (-1003706929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056165719/2000000000 : ℝ)^8249 ≤ (855360264023/2000000000000 : ℝ)^6201 := by
    have hnat : (1056165719 : ℕ)^8249*2000000000000^6201 ≤ 855360264023^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056165719 2000000000 855360264023 2000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105029721/2000000000 : ℝ)^8249 ≤ (45420099527773/100000000000000 : ℝ)^6201 := by
    have hnat : (1105029721 : ℕ)^8249*100000000000000^6201 ≤ 45420099527773^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105029721 2000000000 45420099527773 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003706929/5000000000 : ℝ)^8249 ≤ (5905943628517/50000000000000 : ℝ)^6201 := by
    have hnat : (1003706929 : ℕ)^8249*50000000000000^6201 ≤ 5905943628517^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003706929 5000000000 5905943628517 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056165719/2000000000 : ℝ), (1105029721/2000000000 : ℝ), (-1003706929/5000000000 : ℝ)] ![(855360264023/2000000000000 : ℝ), (45420099527773/100000000000000 : ℝ), (5905943628517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056165719/2000000000 : ℝ)|^8249 ≤ (855360264023/2000000000000 : ℝ)^6201
        have hw : |(1056165719/2000000000 : ℝ)|=(1056165719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105029721/2000000000 : ℝ)|^8249 ≤ (45420099527773/100000000000000 : ℝ)^6201
        have hw : |(1105029721/2000000000 : ℝ)|=(1105029721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003706929/5000000000 : ℝ)|^8249 ≤ (5905943628517/50000000000000 : ℝ)^6201
        have hw : |(-1003706929/5000000000 : ℝ)|=(1003706929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s2_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364419919/10000000000 : ℝ)*x 0 + (296900699/625000000 : ℝ)*x 1 + (4010623947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364419919/10000000000 : ℝ)^8249 ≤ (8297462926313/25000000000000 : ℝ)^6201 := by
    have hnat : (4364419919 : ℕ)^8249*25000000000000^6201 ≤ 8297462926313^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364419919 10000000000 8297462926313 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296900699/625000000 : ℝ)^8249 ≤ (3715056641869/10000000000000 : ℝ)^6201 := by
    have hnat : (296900699 : ℕ)^8249*10000000000000^6201 ≤ 3715056641869^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296900699 625000000 3715056641869 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4010623947/10000000000 : ℝ)^8249 ≤ (5931916372823/20000000000000 : ℝ)^6201 := by
    have hnat : (4010623947 : ℕ)^8249*20000000000000^6201 ≤ 5931916372823^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010623947 10000000000 5931916372823 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364419919/10000000000 : ℝ), (296900699/625000000 : ℝ), (4010623947/10000000000 : ℝ)] ![(8297462926313/25000000000000 : ℝ), (3715056641869/10000000000000 : ℝ), (5931916372823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364419919/10000000000 : ℝ)|^8249 ≤ (8297462926313/25000000000000 : ℝ)^6201
        have hw : |(4364419919/10000000000 : ℝ)|=(4364419919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296900699/625000000 : ℝ)|^8249 ≤ (3715056641869/10000000000000 : ℝ)^6201
        have hw : |(296900699/625000000 : ℝ)|=(296900699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4010623947/10000000000 : ℝ)|^8249 ≤ (5931916372823/20000000000000 : ℝ)^6201
        have hw : |(4010623947/10000000000 : ℝ)|=(4010623947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4331/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2577/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (650673104641899/100000000000000000000 : ℝ) := by
    have hpowers : (2577/50000 : ℝ)^1031 ≤ (650673104641899/100000000000000000000 : ℝ)^256 := by
      have hnat : (2577 : ℕ)^1031*100000000000000000000^256 ≤ 650673104641899^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2577 50000 650673104641899 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2577/50000 : ℝ)) (X := (650673104641899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (20839/100000 : ℝ) ^ (1031/256 : ℝ) ≤ (90334374664546523/50000000000000000000 : ℝ) := by
    have hpowers : (20839/100000 : ℝ)^1031 ≤ (90334374664546523/50000000000000000000 : ℝ)^256 := by
      have hnat : (20839 : ℕ)^1031*50000000000000000000^256 ≤ 90334374664546523^256*100000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20839 100000 90334374664546523 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20839/100000 : ℝ)) (X := (90334374664546523/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000650673104641899/50000000000000000000 : ℝ) ≤ (2500008078152283/2500000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50000650673104641899/50000000000000000000 : ℝ)^256 ≤ (2500008078152283/2500000000000000 : ℝ)^1031 := by
      have hnat : (50000650673104641899 : ℕ)^256*2500000000000000^1031 ≤ 2500008078152283^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000650673104641899 50000000000000000000 2500008078152283 2500000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008078152283/2500000000000000 : ℝ)) (X := (50000650673104641899/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20036263884486746989/20000000000000000000 : ℝ) ≤ (10004499143792317/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (20036263884486746989/20000000000000000000 : ℝ)^256 ≤ (10004499143792317/10000000000000000 : ℝ)^1031 := by
      have hnat : (20036263884486746989 : ℕ)^256*10000000000000000^1031 ≤ 10004499143792317^1031*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20036263884486746989 20000000000000000000 10004499143792317 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004499143792317/10000000000000000 : ℝ)) (X := (20036263884486746989/20000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25090334374664546523/25000000000000000000 : ℝ) ≤ (5004482987487751/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25090334374664546523/25000000000000000000 : ℝ)^256 ≤ (5004482987487751/5000000000000000 : ℝ)^1031 := by
      have hnat : (25090334374664546523 : ℕ)^256*5000000000000000^1031 ≤ 5004482987487751^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25090334374664546523 25000000000000000000 5004482987487751 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004482987487751/5000000000000000 : ℝ)) (X := (25090334374664546523/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(650673104641899/100000000000000000000 : ℝ) ≤ ((3920111568185949111/3921250000000000000 : ℝ)+2*(893366236637/313700000000000 : ℝ)*(2577/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (3920111568185949111/3921250000000000000 : ℝ)+2*(893366236637/313700000000000 : ℝ)*(2577/50000 : ℝ)=(2500008078152283/2500000000000000 : ℝ) by norm_num, show 1+2*(650673104641899/100000000000000000000 : ℝ)=(50000650673104641899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(90334374664546523/50000000000000000000 : ℝ)+(650673104641899/100000000000000000000 : ℝ) ≤ ((3920111568185949111/3921250000000000000 : ℝ)+(893366236637/313700000000000 : ℝ)*((20839/100000 : ℝ)+(2577/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (3920111568185949111/3921250000000000000 : ℝ)+(893366236637/313700000000000 : ℝ)*((20839/100000 : ℝ)+(2577/50000 : ℝ))=(10004499143792317/10000000000000000 : ℝ) by norm_num, show 1+(90334374664546523/50000000000000000000 : ℝ)+(650673104641899/100000000000000000000 : ℝ)=(20036263884486746989/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(90334374664546523/50000000000000000000 : ℝ) ≤ ((3920111568185949111/3921250000000000000 : ℝ)+2*(893366236637/313700000000000 : ℝ)*(20839/100000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (3920111568185949111/3921250000000000000 : ℝ)+2*(893366236637/313700000000000 : ℝ)*(20839/100000 : ℝ)=(5004482987487751/5000000000000000 : ℝ) by norm_num, show 1+2*(90334374664546523/50000000000000000000 : ℝ)=(25090334374664546523/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3920111568185949111/3921250000000000000 : ℝ)*(X 1 0+X 2 0)+(893366236637/313700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (2577/50000 : ℝ)) (hi := (20839/100000 : ℝ)) (c := (3920111568185949111/3921250000000000000 : ℝ)) (alpha := (893366236637/313700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3920111568185949111/3921250000000000000 : ℝ)*(X 0 1+X 2 1)+(893366236637/313700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (2577/50000 : ℝ)) (hi := (20839/100000 : ℝ)) (c := (3920111568185949111/3921250000000000000 : ℝ)) (alpha := (893366236637/313700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3920111568185949111/3921250000000000000 : ℝ)*(X 0 2+X 1 2)+(893366236637/313700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (2577/50000 : ℝ)) (hi := (20839/100000 : ℝ)) (c := (3920111568185949111/3921250000000000000 : ℝ)) (alpha := (893366236637/313700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2188164653/10000000000 : ℝ)*X 0 0+(5527991617/10000000000 : ℝ)*X 0 1+(5144115407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075530789/2000000000 : ℝ)*X 1 0+(-2388445093/10000000000 : ℝ)*X 1 1+(3215073/6250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((672206767/1250000000 : ℝ)*X 2 0+(5144116397/10000000000 : ℝ)*X 2 1+(-597111341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364167757/10000000000 : ℝ)*X 0 0+(4005065753/10000000000 : ℝ)*X 0 1+(297244381/625000000 : ℝ)*X 0 2+(4364167757/10000000000 : ℝ)*X 1 0+(4005065753/10000000000 : ℝ)*X 1 1+(297244381/625000000 : ℝ)*X 1 2+(4364167757/10000000000 : ℝ)*X 2 0+(4005065753/10000000000 : ℝ)*X 2 1+(297244381/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2188293787/10000000000 : ℝ)*X 0 0+(128673221/250000000 : ℝ)*X 0 1+(2762574347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320207089/2500000000 : ℝ)*X 1 0+(-1003706979/5000000000 : ℝ)*X 1 1+(5525148769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056165719/2000000000 : ℝ)*X 2 0+(1105029721/2000000000 : ℝ)*X 2 1+(-1003706929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364419919/10000000000 : ℝ)*X 0 0+(296900699/625000000 : ℝ)*X 0 1+(4010623947/10000000000 : ℝ)*X 0 2+(4364419919/10000000000 : ℝ)*X 1 0+(296900699/625000000 : ℝ)*X 1 1+(4010623947/10000000000 : ℝ)*X 1 2+(4364419919/10000000000 : ℝ)*X 2 0+(296900699/625000000 : ℝ)*X 2 1+(4010623947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (526214789444782804236912951/98031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23827227/20000000000000 : ℝ)*(base1) + (247463297/10000000000000 : ℝ)*(base19) + (51343161/2000000000000 : ℝ)*(base23) + (10027383/3125000000000 : ℝ)*(upper3) + (91873219/50000000000000 : ℝ)*(upper5) + (984231351492451/50000000000000 : ℝ)*(major0) + (984231351492451/50000000000000 : ℝ)*(major1) + (984231351492451/50000000000000 : ℝ)*(major2) + (130251951172273/5000000000000 : ℝ)*(sp0) + (1302533730252311/50000000000000 : ℝ)*(sp1) + (1302533683989771/50000000000000 : ℝ)*(sp2) + (1331843896686111/100000000000000 : ℝ)*(sp3) + (7757707067/25000000000000 : ℝ)*(sp4) + (11276082393/100000000000000 : ℝ)*(sp7) + (2081023893601/156250000000 : ℝ)*(f.failure) + (325633741892199/12500000000000 : ℝ)*(f.sum) + (5148249237361/3921250000000000000000000000 : ℝ)*base65 + (1283451187603061061/196062500000000000000000000000000 : ℝ)*base67 + (182574326606311061/196062500000000000000000000000000 : ℝ)*base69 + (2190231398077248561/196062500000000000000000000000000 : ℝ)*base71 + (49559942786009/15685000000000000000000000000 : ℝ)*base73 + (414091712721561061/196062500000000000000000000000000 : ℝ)*base75 + (1050980455620123561/196062500000000000000000000000000 : ℝ)*base77 + (544375510224436061/196062500000000000000000000000000 : ℝ)*base79 + (21763323170359/15685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3879/7812500000000000000 : ℝ)*base90 + (3879/7812500000000000000 : ℝ)*base92 + (3879/7812500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262095693189308530646108553/49015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (507251731/50000000000000 : ℝ)*(base19) + (120691911/10000000000000 : ℝ)*(base23) + (73156243/50000000000000 : ℝ)*(upper3) + (21793909/100000000000000 : ℝ)*(lower4) + (5788533/5000000000000 : ℝ)*(upper5) + (31216447109799/1562500000000 : ℝ)*(major0) + (31216447109799/1562500000000 : ℝ)*(major1) + (31216447109799/1562500000000 : ℝ)*(major2) + (8594881317/100000000000000 : ℝ)*(sp1) + (5156036793/50000000000000 : ℝ)*(sp2) + (264396464355877/10000000000000 : ℝ)*(sp4) + (2643955034173991/100000000000000 : ℝ)*(sp5) + (1321976562283037/50000000000000 : ℝ)*(sp6) + (675870204127973/50000000000000 : ℝ)*(sp7) + (675870204127973/50000000000000 : ℝ)*(f.failure) + (264396464355877/10000000000000 : ℝ)*(f.sum) + (380761346787/980312500000000000000000000 : ℝ)*base65 + (1783648985867561/6126953125000000000000000000000 : ℝ)*base68 + (148498385839451631/24507812500000000000000000000000 : ℝ)*base69 + (41143174561075137/49015625000000000000000000000000 : ℝ)*base71 + (24661081443793/15685000000000000000000000000 : ℝ)*base74 + (173793728866981387/49015625000000000000000000000000 : ℝ)*base75 + (20664810999624253/12253906250000000000000000000000 : ℝ)*base77 + (31220560912531997/12253906250000000000000000000000 : ℝ)*base80 + (4397324648211/7842500000000000000000000000 : ℝ)*base81 + (4592317/2500000000000000000000 : ℝ)*base90 + (4592317/2500000000000000000000 : ℝ)*base92 + (4592317/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1056_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1056_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1056_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1056_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1056_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

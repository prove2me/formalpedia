-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1625_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:06.419751+00:00
-- url     : https://prove2.me/submissions/64d15f42-5cbe-45e2-8e74-52f4831d24cb

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
theorem support_rectangle_w1625_s3_0 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416792001/2500000000 : ℝ)*x 0 + (681905831/1250000000 : ℝ)*x 1 + (5181844611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416792001/2500000000 : ℝ)^4819 ≤ (5140638423047/50000000000000 : ℝ)^3795 := by
    have hnat : (416792001 : ℕ)^4819*50000000000000^3795 ≤ 5140638423047^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416792001 2500000000 5140638423047 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681905831/1250000000 : ℝ)^4819 ≤ (2316164276499/5000000000000 : ℝ)^3795 := by
    have hnat : (681905831 : ℕ)^4819*5000000000000^3795 ≤ 2316164276499^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681905831 1250000000 2316164276499 5000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181844611/10000000000 : ℝ)^4819 ≤ (21697718803087/50000000000000 : ℝ)^3795 := by
    have hnat : (5181844611 : ℕ)^4819*50000000000000^3795 ≤ 21697718803087^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181844611 10000000000 21697718803087 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416792001/2500000000 : ℝ), (681905831/1250000000 : ℝ), (5181844611/10000000000 : ℝ)] ![(5140638423047/50000000000000 : ℝ), (2316164276499/5000000000000 : ℝ), (21697718803087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416792001/2500000000 : ℝ)|^4819 ≤ (5140638423047/50000000000000 : ℝ)^3795
        have hw : |(-416792001/2500000000 : ℝ)|=(416792001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681905831/1250000000 : ℝ)|^4819 ≤ (2316164276499/5000000000000 : ℝ)^3795
        have hw : |(681905831/1250000000 : ℝ)|=(681905831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181844611/10000000000 : ℝ)|^4819 ≤ (21697718803087/50000000000000 : ℝ)^3795
        have hw : |(5181844611/10000000000 : ℝ)|=(5181844611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_1 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675755109/5000000000 : ℝ)*x 0 + (-226008101/1250000000 : ℝ)*x 1 + (1295461153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675755109/5000000000 : ℝ)^4819 ≤ (45207603154613/100000000000000 : ℝ)^3795 := by
    have hnat : (2675755109 : ℕ)^4819*100000000000000^3795 ≤ 45207603154613^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675755109 5000000000 45207603154613 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226008101/1250000000 : ℝ)^4819 ≤ (455878368759/4000000000000 : ℝ)^3795 := by
    have hnat : (226008101 : ℕ)^4819*4000000000000^3795 ≤ 455878368759^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226008101 1250000000 455878368759 4000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295461153/2500000000 : ℝ)^4819 ≤ (43395437616809/100000000000000 : ℝ)^3795 := by
    have hnat : (1295461153 : ℕ)^4819*100000000000000^3795 ≤ 43395437616809^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295461153 2500000000 43395437616809 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675755109/5000000000 : ℝ), (-226008101/1250000000 : ℝ), (1295461153/2500000000 : ℝ)] ![(45207603154613/100000000000000 : ℝ), (455878368759/4000000000000 : ℝ), (43395437616809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675755109/5000000000 : ℝ)|^4819 ≤ (45207603154613/100000000000000 : ℝ)^3795
        have hw : |(2675755109/5000000000 : ℝ)|=(2675755109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226008101/1250000000 : ℝ)|^4819 ≤ (455878368759/4000000000000 : ℝ)^3795
        have hw : |(-226008101/1250000000 : ℝ)|=(226008101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295461153/2500000000 : ℝ)|^4819 ≤ (43395437616809/100000000000000 : ℝ)^3795
        have hw : |(1295461153/2500000000 : ℝ)|=(1295461153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_2 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675755109/5000000000 : ℝ)*x 0 + (1295461153/2500000000 : ℝ)*x 1 + (-226008101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675755109/5000000000 : ℝ)^4819 ≤ (45207603154613/100000000000000 : ℝ)^3795 := by
    have hnat : (2675755109 : ℕ)^4819*100000000000000^3795 ≤ 45207603154613^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675755109 5000000000 45207603154613 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295461153/2500000000 : ℝ)^4819 ≤ (43395437616809/100000000000000 : ℝ)^3795 := by
    have hnat : (1295461153 : ℕ)^4819*100000000000000^3795 ≤ 43395437616809^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295461153 2500000000 43395437616809 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226008101/1250000000 : ℝ)^4819 ≤ (455878368759/4000000000000 : ℝ)^3795 := by
    have hnat : (226008101 : ℕ)^4819*4000000000000^3795 ≤ 455878368759^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226008101 1250000000 455878368759 4000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675755109/5000000000 : ℝ), (1295461153/2500000000 : ℝ), (-226008101/1250000000 : ℝ)] ![(45207603154613/100000000000000 : ℝ), (43395437616809/100000000000000 : ℝ), (455878368759/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675755109/5000000000 : ℝ)|^4819 ≤ (45207603154613/100000000000000 : ℝ)^3795
        have hw : |(2675755109/5000000000 : ℝ)|=(2675755109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295461153/2500000000 : ℝ)|^4819 ≤ (43395437616809/100000000000000 : ℝ)^3795
        have hw : |(1295461153/2500000000 : ℝ)|=(1295461153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226008101/1250000000 : ℝ)|^4819 ≤ (455878368759/4000000000000 : ℝ)^3795
        have hw : |(-226008101/1250000000 : ℝ)|=(226008101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_3 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840059733/2000000000 : ℝ)*x 0 + (154729909/400000000 : ℝ)*x 1 + (4553378431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840059733/2000000000 : ℝ)^4819 ≤ (1661882623721/5000000000000 : ℝ)^3795 := by
    have hnat : (840059733 : ℕ)^4819*5000000000000^3795 ≤ 1661882623721^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840059733 2000000000 1661882623721 5000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154729909/400000000 : ℝ)^4819 ≤ (7484344893891/25000000000000 : ℝ)^3795 := by
    have hnat : (154729909 : ℕ)^4819*25000000000000^3795 ≤ 7484344893891^3795*400000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154729909 400000000 7484344893891 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4553378431/10000000000 : ℝ)^4819 ≤ (9206241983101/25000000000000 : ℝ)^3795 := by
    have hnat : (4553378431 : ℕ)^4819*25000000000000^3795 ≤ 9206241983101^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553378431 10000000000 9206241983101 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840059733/2000000000 : ℝ), (154729909/400000000 : ℝ), (4553378431/10000000000 : ℝ)] ![(1661882623721/5000000000000 : ℝ), (7484344893891/25000000000000 : ℝ), (9206241983101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840059733/2000000000 : ℝ)|^4819 ≤ (1661882623721/5000000000000 : ℝ)^3795
        have hw : |(840059733/2000000000 : ℝ)|=(840059733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154729909/400000000 : ℝ)|^4819 ≤ (7484344893891/25000000000000 : ℝ)^3795
        have hw : |(154729909/400000000 : ℝ)|=(154729909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4553378431/10000000000 : ℝ)|^4819 ≤ (9206241983101/25000000000000 : ℝ)^3795
        have hw : |(4553378431/10000000000 : ℝ)|=(4553378431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_4 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-833618187/5000000000 : ℝ)*x 0 + (1036778981/2000000000 : ℝ)*x 1 + (1090634947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833618187/5000000000 : ℝ)^4819 ≤ (10281812249113/100000000000000 : ℝ)^3795 := by
    have hnat : (833618187 : ℕ)^4819*100000000000000^3795 ≤ 10281812249113^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833618187 5000000000 10281812249113 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036778981/2000000000 : ℝ)^4819 ≤ (8683448401369/20000000000000 : ℝ)^3795 := by
    have hnat : (1036778981 : ℕ)^4819*20000000000000^3795 ≤ 8683448401369^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036778981 2000000000 8683448401369 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090634947/2000000000 : ℝ)^4819 ≤ (46300945725453/100000000000000 : ℝ)^3795 := by
    have hnat : (1090634947 : ℕ)^4819*100000000000000^3795 ≤ 46300945725453^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090634947 2000000000 46300945725453 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-833618187/5000000000 : ℝ), (1036778981/2000000000 : ℝ), (1090634947/2000000000 : ℝ)] ![(10281812249113/100000000000000 : ℝ), (8683448401369/20000000000000 : ℝ), (46300945725453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-833618187/5000000000 : ℝ)|^4819 ≤ (10281812249113/100000000000000 : ℝ)^3795
        have hw : |(-833618187/5000000000 : ℝ)|=(833618187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036778981/2000000000 : ℝ)|^4819 ≤ (8683448401369/20000000000000 : ℝ)^3795
        have hw : |(1036778981/2000000000 : ℝ)|=(1036778981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090634947/2000000000 : ℝ)|^4819 ≤ (46300945725453/100000000000000 : ℝ)^3795
        have hw : |(1090634947/2000000000 : ℝ)|=(1090634947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_5 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639359067/5000000000 : ℝ)*x 0 + (-1536734687/10000000000 : ℝ)*x 1 + (5453174733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639359067/5000000000 : ℝ)^4819 ≤ (8885639322893/20000000000000 : ℝ)^3795 := by
    have hnat : (2639359067 : ℕ)^4819*20000000000000^3795 ≤ 8885639322893^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639359067 5000000000 8885639322893 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1536734687/10000000000 : ℝ)^4819 ≤ (9270857664059/100000000000000 : ℝ)^3795 := by
    have hnat : (1536734687 : ℕ)^4819*100000000000000^3795 ≤ 9270857664059^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536734687 10000000000 9270857664059 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453174733/10000000000 : ℝ)^4819 ≤ (46300945703889/100000000000000 : ℝ)^3795 := by
    have hnat : (5453174733 : ℕ)^4819*100000000000000^3795 ≤ 46300945703889^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453174733 10000000000 46300945703889 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639359067/5000000000 : ℝ), (-1536734687/10000000000 : ℝ), (5453174733/10000000000 : ℝ)] ![(8885639322893/20000000000000 : ℝ), (9270857664059/100000000000000 : ℝ), (46300945703889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639359067/5000000000 : ℝ)|^4819 ≤ (8885639322893/20000000000000 : ℝ)^3795
        have hw : |(2639359067/5000000000 : ℝ)|=(2639359067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1536734687/10000000000 : ℝ)|^4819 ≤ (9270857664059/100000000000000 : ℝ)^3795
        have hw : |(-1536734687/10000000000 : ℝ)|=(1536734687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453174733/10000000000 : ℝ)|^4819 ≤ (46300945703889/100000000000000 : ℝ)^3795
        have hw : |(5453174733/10000000000 : ℝ)|=(5453174733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_6 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659839767/1250000000 : ℝ)*x 0 + (1363293683/2500000000 : ℝ)*x 1 + (-1536734687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659839767/1250000000 : ℝ)^4819 ≤ (138838114487/312500000000 : ℝ)^3795 := by
    have hnat : (659839767 : ℕ)^4819*312500000000^3795 ≤ 138838114487^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659839767 1250000000 138838114487 312500000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363293683/2500000000 : ℝ)^4819 ≤ (11575236423277/25000000000000 : ℝ)^3795 := by
    have hnat : (1363293683 : ℕ)^4819*25000000000000^3795 ≤ 11575236423277^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363293683 2500000000 11575236423277 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1536734687/10000000000 : ℝ)^4819 ≤ (9270857664059/100000000000000 : ℝ)^3795 := by
    have hnat : (1536734687 : ℕ)^4819*100000000000000^3795 ≤ 9270857664059^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536734687 10000000000 9270857664059 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659839767/1250000000 : ℝ), (1363293683/2500000000 : ℝ), (-1536734687/10000000000 : ℝ)] ![(138838114487/312500000000 : ℝ), (11575236423277/25000000000000 : ℝ), (9270857664059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659839767/1250000000 : ℝ)|^4819 ≤ (138838114487/312500000000 : ℝ)^3795
        have hw : |(659839767/1250000000 : ℝ)|=(659839767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363293683/2500000000 : ℝ)|^4819 ≤ (11575236423277/25000000000000 : ℝ)^3795
        have hw : |(1363293683/2500000000 : ℝ)|=(1363293683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1536734687/10000000000 : ℝ)|^4819 ≤ (9270857664059/100000000000000 : ℝ)^3795
        have hw : |(-1536734687/10000000000 : ℝ)|=(1536734687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s3_7 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2100234999/5000000000 : ℝ)*x 0 + (568530063/1250000000 : ℝ)*x 1 + (3873439829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100234999/5000000000 : ℝ)^4819 ≤ (1329574964003/4000000000000 : ℝ)^3795 := by
    have hnat : (2100234999 : ℕ)^4819*4000000000000^3795 ≤ 1329574964003^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100234999 5000000000 1329574964003 4000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568530063/1250000000 : ℝ)^4819 ≤ (36772211481777/100000000000000 : ℝ)^3795 := by
    have hnat : (568530063 : ℕ)^4819*100000000000000^3795 ≤ 36772211481777^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568530063 1250000000 36772211481777 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3873439829/10000000000 : ℝ)^4819 ≤ (29988414402497/100000000000000 : ℝ)^3795 := by
    have hnat : (3873439829 : ℕ)^4819*100000000000000^3795 ≤ 29988414402497^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3873439829 10000000000 29988414402497 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100234999/5000000000 : ℝ), (568530063/1250000000 : ℝ), (3873439829/10000000000 : ℝ)] ![(1329574964003/4000000000000 : ℝ), (36772211481777/100000000000000 : ℝ), (29988414402497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100234999/5000000000 : ℝ)|^4819 ≤ (1329574964003/4000000000000 : ℝ)^3795
        have hw : |(2100234999/5000000000 : ℝ)|=(2100234999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568530063/1250000000 : ℝ)|^4819 ≤ (36772211481777/100000000000000 : ℝ)^3795
        have hw : |(568530063/1250000000 : ℝ)|=(568530063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3873439829/10000000000 : ℝ)|^4819 ≤ (29988414402497/100000000000000 : ℝ)^3795
        have hw : |(3873439829/10000000000 : ℝ)|=(3873439829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1625_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5261/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4081/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8217/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8217/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8217/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8217/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8217/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8217/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10423/100000 : ℝ) ^ (4815/1024 : ℝ) ≤ (1206218793208549/50000000000000000000 : ℝ) := by
    have hpowers : (10423/100000 : ℝ)^4815 ≤ (1206218793208549/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10423 : ℕ)^4815*50000000000000000000^1024 ≤ 1206218793208549^1024*100000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10423 100000 1206218793208549 50000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10423/100000 : ℝ)) (X := (1206218793208549/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8217/50000 : ℝ) ^ (4815/1024 : ℝ) ≤ (20526197431478849/100000000000000000000 : ℝ) := by
    have hpowers : (8217/50000 : ℝ)^4815 ≤ (20526197431478849/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8217 : ℕ)^4815*100000000000000000000^1024 ≤ 20526197431478849^1024*50000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8217 50000 20526197431478849 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8217/50000 : ℝ)) (X := (20526197431478849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001206218793208549/25000000000000000000 : ℝ) ≤ (2000020521613031/2000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (25001206218793208549/25000000000000000000 : ℝ)^1024 ≤ (2000020521613031/2000000000000000 : ℝ)^4815 := by
      have hnat : (25001206218793208549 : ℕ)^1024*2000000000000000^4815 ≤ 2000020521613031^4815*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001206218793208549 25000000000000000000 2000020521613031 2000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000020521613031/2000000000000000 : ℝ)) (X := (25001206218793208549/25000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022938635017895947/100000000000000000000 : ℝ) ≤ (500024389451133/500000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (100022938635017895947/100000000000000000000 : ℝ)^1024 ≤ (500024389451133/500000000000000 : ℝ)^4815 := by
      have hnat : (100022938635017895947 : ℕ)^1024*500000000000000^4815 ≤ 500024389451133^4815*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022938635017895947 100000000000000000000 500024389451133 500000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500024389451133/500000000000000 : ℝ)) (X := (100022938635017895947/100000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020526197431478849/50000000000000000000 : ℝ) ≤ (2000174593996033/2000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50020526197431478849/50000000000000000000 : ℝ)^1024 ≤ (2000174593996033/2000000000000000 : ℝ)^4815 := by
      have hnat : (50020526197431478849 : ℕ)^1024*2000000000000000^4815 ≤ 2000174593996033^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020526197431478849 50000000000000000000 2000174593996033 2000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000174593996033/2000000000000000 : ℝ)) (X := (50020526197431478849/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1206218793208549/50000000000000000000 : ℝ) ≤ ((2404103491793579899/2404400000000000000 : ℝ)+2*(77036191501/120220000000000 : ℝ)*(10423/100000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (2404103491793579899/2404400000000000000 : ℝ)+2*(77036191501/120220000000000 : ℝ)*(10423/100000 : ℝ)=(2000020521613031/2000000000000000 : ℝ) by norm_num, show 1+2*(1206218793208549/50000000000000000000 : ℝ)=(25001206218793208549/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20526197431478849/100000000000000000000 : ℝ)+(1206218793208549/50000000000000000000 : ℝ) ≤ ((2404103491793579899/2404400000000000000 : ℝ)+(77036191501/120220000000000 : ℝ)*((8217/50000 : ℝ)+(10423/100000 : ℝ)))^(4815/1024 : ℝ) := by
    rw [show (2404103491793579899/2404400000000000000 : ℝ)+(77036191501/120220000000000 : ℝ)*((8217/50000 : ℝ)+(10423/100000 : ℝ))=(500024389451133/500000000000000 : ℝ) by norm_num, show 1+(20526197431478849/100000000000000000000 : ℝ)+(1206218793208549/50000000000000000000 : ℝ)=(100022938635017895947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20526197431478849/100000000000000000000 : ℝ) ≤ ((2404103491793579899/2404400000000000000 : ℝ)+2*(77036191501/120220000000000 : ℝ)*(8217/50000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (2404103491793579899/2404400000000000000 : ℝ)+2*(77036191501/120220000000000 : ℝ)*(8217/50000 : ℝ)=(2000174593996033/2000000000000000 : ℝ) by norm_num, show 1+2*(20526197431478849/100000000000000000000 : ℝ)=(50020526197431478849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2404103491793579899/2404400000000000000 : ℝ)*(X 1 0+X 2 0)+(77036191501/120220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (10423/100000 : ℝ)) (hi := (8217/50000 : ℝ)) (c := (2404103491793579899/2404400000000000000 : ℝ)) (alpha := (77036191501/120220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2404103491793579899/2404400000000000000 : ℝ)*(X 0 1+X 2 1)+(77036191501/120220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (10423/100000 : ℝ)) (hi := (8217/50000 : ℝ)) (c := (2404103491793579899/2404400000000000000 : ℝ)) (alpha := (77036191501/120220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2404103491793579899/2404400000000000000 : ℝ)*(X 0 2+X 1 2)+(77036191501/120220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (10423/100000 : ℝ)) (hi := (8217/50000 : ℝ)) (c := (2404103491793579899/2404400000000000000 : ℝ)) (alpha := (77036191501/120220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416792001/2500000000 : ℝ)*X 0 0+(681905831/1250000000 : ℝ)*X 0 1+(5181844611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675755109/5000000000 : ℝ)*X 1 0+(-226008101/1250000000 : ℝ)*X 1 1+(1295461153/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675755109/5000000000 : ℝ)*X 2 0+(1295461153/2500000000 : ℝ)*X 2 1+(-226008101/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840059733/2000000000 : ℝ)*X 0 0+(154729909/400000000 : ℝ)*X 0 1+(4553378431/10000000000 : ℝ)*X 0 2+(840059733/2000000000 : ℝ)*X 1 0+(154729909/400000000 : ℝ)*X 1 1+(4553378431/10000000000 : ℝ)*X 1 2+(840059733/2000000000 : ℝ)*X 2 0+(154729909/400000000 : ℝ)*X 2 1+(4553378431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-833618187/5000000000 : ℝ)*X 0 0+(1036778981/2000000000 : ℝ)*X 0 1+(1090634947/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639359067/5000000000 : ℝ)*X 1 0+(-1536734687/10000000000 : ℝ)*X 1 1+(5453174733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659839767/1250000000 : ℝ)*X 2 0+(1363293683/2500000000 : ℝ)*X 2 1+(-1536734687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2100234999/5000000000 : ℝ)*X 0 0+(568530063/1250000000 : ℝ)*X 0 1+(3873439829/10000000000 : ℝ)*X 0 2+(2100234999/5000000000 : ℝ)*X 1 0+(568530063/1250000000 : ℝ)*X 1 1+(3873439829/10000000000 : ℝ)*X 1 2+(2100234999/5000000000 : ℝ)*X 2 0+(568530063/1250000000 : ℝ)*X 2 1+(3873439829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33934425113925822985059/6011000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229749199/25000000000000 : ℝ)*(base19) + (1719799/200000000000 : ℝ)*(base23) + (31625979/100000000000000 : ℝ)*(lower2) + (69769589/50000000000000 : ℝ)*(upper3) + (19324729/20000000000000 : ℝ)*(upper5) + (1279306201943669/50000000000000 : ℝ)*(major0) + (1279306201943669/50000000000000 : ℝ)*(major1) + (1279306201943669/50000000000000 : ℝ)*(major2) + (91440719368907/2500000000000 : ℝ)*(sp0) + (18288195227897/500000000000 : ℝ)*(sp1) + (457204888084587/12500000000000 : ℝ)*(sp2) + (1459579811051361/100000000000000 : ℝ)*(sp3) + (11189819917/100000000000000 : ℝ)*(sp4) + (2421983761/50000000000000 : ℝ)*(sp7) + (1459584655018883/100000000000000 : ℝ)*(f.failure) + (914409991144049/25000000000000 : ℝ)*(f.sum) + (9696821864993/1202200000000000000000000000 : ℝ)*base65 + (717063285138270569/120220000000000000000000000000000 : ℝ)*base68 + (105245103016790569/120220000000000000000000000000000 : ℝ)*base70 + (186635824316530569/120220000000000000000000000000000 : ℝ)*base72 + (3323301256119/1202200000000000000000000000 : ℝ)*base73 + (692103380463709431/120220000000000000000000000000000 : ℝ)*base75 + (606795674807309431/120220000000000000000000000000000 : ℝ)*base77 + (235224625903789431/120220000000000000000000000000000 : ℝ)*base79 + (11236935694767/6011000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (45598699/5000000000000000000000 : ℝ)*base90 + (45598699/5000000000000000000000 : ℝ)*base92 + (45598699/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288787300935989622633544533/30055000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1452041971/100000000000000 : ℝ)*(base19) + (1573089763/100000000000000 : ℝ)*(base23) + (201633599/100000000000000 : ℝ)*(upper3) + (53869429/100000000000000 : ℝ)*(lower4) + (199755631/100000000000000 : ℝ)*(upper5) + (1298881845570411/50000000000000 : ℝ)*(major0) + (1298881845570411/50000000000000 : ℝ)*(major1) + (1298881845570411/50000000000000 : ℝ)*(major2) + (16873975857/100000000000000 : ℝ)*(sp1) + (18149605021/100000000000000 : ℝ)*(sp2) + (464201023089699/12500000000000 : ℝ)*(sp4) + (928397464674941/25000000000000 : ℝ)*(sp5) + (464198557752851/12500000000000 : ℝ)*(sp6) + (92619929829779/6250000000000 : ℝ)*(sp7) + (92619929829779/6250000000000 : ℝ)*(f.failure) + (464201023089699/12500000000000 : ℝ)*(f.sum) + (12893690611241/3005500000000000000000000000 : ℝ)*base66 + (611055524321468489/120220000000000000000000000000000 : ℝ)*base67 + (591717396766268489/120220000000000000000000000000000 : ℝ)*base69 + (167938110076708489/120220000000000000000000000000000 : ℝ)*base71 + (1060076108297/601100000000000000000000000 : ℝ)*base73 + (19836618976451511/120220000000000000000000000000000 : ℝ)*base76 + (471887539278628489/120220000000000000000000000000000 : ℝ)*base77 + (351666983140908489/120220000000000000000000000000000 : ℝ)*base79 + (2103572736669/601100000000000000000000000 : ℝ)*base82 + (909013/312500000000000000000 : ℝ)*base89 + (909013/312500000000000000000 : ℝ)*base91 + (909013/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1625_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4081/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1625_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1625_s4_0 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-833624883/5000000000 : ℝ)*x 0 + (218193347/400000000 : ℝ)*x 1 + (5182203137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833624883/5000000000 : ℝ)^4819 ≤ (10281917122079/100000000000000 : ℝ)^3795 := by
    have hnat : (833624883 : ℕ)^4819*100000000000000^3795 ≤ 10281917122079^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833624883 5000000000 10281917122079 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218193347/400000000 : ℝ)^4819 ≤ (9263766516993/20000000000000 : ℝ)^3795 := by
    have hnat : (218193347 : ℕ)^4819*20000000000000^3795 ≤ 9263766516993^3795*400000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218193347 400000000 9263766516993 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182203137/10000000000 : ℝ)^4819 ≤ (43399250279029/100000000000000 : ℝ)^3795 := by
    have hnat : (5182203137 : ℕ)^4819*100000000000000^3795 ≤ 43399250279029^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182203137 10000000000 43399250279029 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-833624883/5000000000 : ℝ), (218193347/400000000 : ℝ), (5182203137/10000000000 : ℝ)] ![(10281917122079/100000000000000 : ℝ), (9263766516993/20000000000000 : ℝ), (43399250279029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-833624883/5000000000 : ℝ)|^4819 ≤ (10281917122079/100000000000000 : ℝ)^3795
        have hw : |(-833624883/5000000000 : ℝ)|=(833624883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218193347/400000000 : ℝ)|^4819 ≤ (9263766516993/20000000000000 : ℝ)^3795
        have hw : |(218193347/400000000 : ℝ)|=(218193347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182203137/10000000000 : ℝ)|^4819 ≤ (43399250279029/100000000000000 : ℝ)^3795
        have hw : |(5182203137/10000000000 : ℝ)|=(5182203137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_1 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337849849/2500000000 : ℝ)*x 0 + (-903868803/5000000000 : ℝ)*x 1 + (323887667/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337849849/2500000000 : ℝ)^4819 ≤ (45206414364897/100000000000000 : ℝ)^3795 := by
    have hnat : (1337849849 : ℕ)^4819*100000000000000^3795 ≤ 45206414364897^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337849849 2500000000 45206414364897 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903868803/5000000000 : ℝ)^4819 ≤ (11394340279313/100000000000000 : ℝ)^3795 := by
    have hnat : (903868803 : ℕ)^4819*100000000000000^3795 ≤ 11394340279313^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903868803 5000000000 11394340279313 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323887667/625000000 : ℝ)^4819 ≤ (21699622667017/50000000000000 : ℝ)^3795 := by
    have hnat : (323887667 : ℕ)^4819*50000000000000^3795 ≤ 21699622667017^3795*625000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323887667 625000000 21699622667017 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337849849/2500000000 : ℝ), (-903868803/5000000000 : ℝ), (323887667/625000000 : ℝ)] ![(45206414364897/100000000000000 : ℝ), (11394340279313/100000000000000 : ℝ), (21699622667017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337849849/2500000000 : ℝ)|^4819 ≤ (45206414364897/100000000000000 : ℝ)^3795
        have hw : |(1337849849/2500000000 : ℝ)|=(1337849849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903868803/5000000000 : ℝ)|^4819 ≤ (11394340279313/100000000000000 : ℝ)^3795
        have hw : |(-903868803/5000000000 : ℝ)|=(903868803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323887667/625000000 : ℝ)|^4819 ≤ (21699622667017/50000000000000 : ℝ)^3795
        have hw : |(323887667/625000000 : ℝ)|=(323887667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_2 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351399027/10000000000 : ℝ)*x 0 + (2591101563/5000000000 : ℝ)*x 1 + (-903868749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351399027/10000000000 : ℝ)^4819 ≤ (22603205203319/50000000000000 : ℝ)^3795 := by
    have hnat : (5351399027 : ℕ)^4819*50000000000000^3795 ≤ 22603205203319^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351399027 10000000000 22603205203319 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591101563/5000000000 : ℝ)^4819 ≤ (43399250162051/100000000000000 : ℝ)^3795 := by
    have hnat : (2591101563 : ℕ)^4819*100000000000000^3795 ≤ 43399250162051^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591101563 5000000000 43399250162051 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903868749/5000000000 : ℝ)^4819 ≤ (11394339414897/100000000000000 : ℝ)^3795 := by
    have hnat : (903868749 : ℕ)^4819*100000000000000^3795 ≤ 11394339414897^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903868749 5000000000 11394339414897 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351399027/10000000000 : ℝ), (2591101563/5000000000 : ℝ), (-903868749/5000000000 : ℝ)] ![(22603205203319/50000000000000 : ℝ), (43399250162051/100000000000000 : ℝ), (11394339414897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351399027/10000000000 : ℝ)|^4819 ≤ (22603205203319/50000000000000 : ℝ)^3795
        have hw : |(5351399027/10000000000 : ℝ)|=(5351399027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591101563/5000000000 : ℝ)|^4819 ≤ (43399250162051/100000000000000 : ℝ)^3795
        have hw : |(2591101563/5000000000 : ℝ)|=(2591101563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903868749/5000000000 : ℝ)|^4819 ≤ (11394339414897/100000000000000 : ℝ)^3795
        have hw : |(-903868749/5000000000 : ℝ)|=(903868749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_3 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2100176149/5000000000 : ℝ)*x 0 + (3869207823/10000000000 : ℝ)*x 1 + (36419257/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100176149/5000000000 : ℝ)^4819 ≤ (16619095699601/50000000000000 : ℝ)^3795 := by
    have hnat : (2100176149 : ℕ)^4819*50000000000000^3795 ≤ 16619095699601^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100176149 5000000000 16619095699601 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3869207823/10000000000 : ℝ)^4819 ≤ (14973407644661/50000000000000 : ℝ)^3795 := by
    have hnat : (3869207823 : ℕ)^4819*50000000000000^3795 ≤ 14973407644661^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3869207823 10000000000 14973407644661 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36419257/80000000 : ℝ)^4819 ≤ (36814993289669/100000000000000 : ℝ)^3795 := by
    have hnat : (36419257 : ℕ)^4819*100000000000000^3795 ≤ 36814993289669^3795*80000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36419257 80000000 36814993289669 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100176149/5000000000 : ℝ), (3869207823/10000000000 : ℝ), (36419257/80000000 : ℝ)] ![(16619095699601/50000000000000 : ℝ), (14973407644661/50000000000000 : ℝ), (36814993289669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100176149/5000000000 : ℝ)|^4819 ≤ (16619095699601/50000000000000 : ℝ)^3795
        have hw : |(2100176149/5000000000 : ℝ)|=(2100176149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3869207823/10000000000 : ℝ)|^4819 ≤ (14973407644661/50000000000000 : ℝ)^3795
        have hw : |(3869207823/10000000000 : ℝ)|=(3869207823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36419257/80000000 : ℝ)|^4819 ≤ (36814993289669/100000000000000 : ℝ)^3795
        have hw : |(36419257/80000000 : ℝ)|=(36419257/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_4 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416829417/2500000000 : ℝ)*x 0 + (1036848323/2000000000 : ℝ)*x 1 + (5452773677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416829417/2500000000 : ℝ)^4819 ≤ (5141224433611/50000000000000 : ℝ)^3795 := by
    have hnat : (416829417 : ℕ)^4819*50000000000000^3795 ≤ 5141224433611^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416829417 2500000000 5141224433611 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036848323/2000000000 : ℝ)^4819 ≤ (43420929417249/100000000000000 : ℝ)^3795 := by
    have hnat : (1036848323 : ℕ)^4819*100000000000000^3795 ≤ 43420929417249^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036848323 2000000000 43420929417249 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452773677/10000000000 : ℝ)^4819 ≤ (46296621697743/100000000000000 : ℝ)^3795 := by
    have hnat : (5452773677 : ℕ)^4819*100000000000000^3795 ≤ 46296621697743^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452773677 10000000000 46296621697743 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416829417/2500000000 : ℝ), (1036848323/2000000000 : ℝ), (5452773677/10000000000 : ℝ)] ![(5141224433611/50000000000000 : ℝ), (43420929417249/100000000000000 : ℝ), (46296621697743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416829417/2500000000 : ℝ)|^4819 ≤ (5141224433611/50000000000000 : ℝ)^3795
        have hw : |(-416829417/2500000000 : ℝ)|=(416829417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036848323/2000000000 : ℝ)|^4819 ≤ (43420929417249/100000000000000 : ℝ)^3795
        have hw : |(1036848323/2000000000 : ℝ)|=(1036848323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452773677/10000000000 : ℝ)|^4819 ≤ (46296621697743/100000000000000 : ℝ)^3795
        have hw : |(5452773677/10000000000 : ℝ)|=(5452773677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_5 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278813021/10000000000 : ℝ)*x 0 + (-1537166737/10000000000 : ℝ)*x 1 + (218110947/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278813021/10000000000 : ℝ)^4819 ≤ (2221460535997/5000000000000 : ℝ)^3795 := by
    have hnat : (5278813021 : ℕ)^4819*5000000000000^3795 ≤ 2221460535997^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278813021 10000000000 2221460535997 5000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537166737/10000000000 : ℝ)^4819 ≤ (1159270947197/12500000000000 : ℝ)^3795 := by
    have hnat : (1537166737 : ℕ)^4819*12500000000000^3795 ≤ 1159270947197^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537166737 10000000000 1159270947197 12500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218110947/400000000 : ℝ)^4819 ≤ (2314831083809/5000000000000 : ℝ)^3795 := by
    have hnat : (218110947 : ℕ)^4819*5000000000000^3795 ≤ 2314831083809^3795*400000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218110947 400000000 2314831083809 5000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278813021/10000000000 : ℝ), (-1537166737/10000000000 : ℝ), (218110947/400000000 : ℝ)] ![(2221460535997/5000000000000 : ℝ), (1159270947197/12500000000000 : ℝ), (2314831083809/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278813021/10000000000 : ℝ)|^4819 ≤ (2221460535997/5000000000000 : ℝ)^3795
        have hw : |(5278813021/10000000000 : ℝ)|=(5278813021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1537166737/10000000000 : ℝ)|^4819 ≤ (1159270947197/12500000000000 : ℝ)^3795
        have hw : |(-1537166737/10000000000 : ℝ)|=(1537166737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218110947/400000000 : ℝ)|^4819 ≤ (2314831083809/5000000000000 : ℝ)^3795
        have hw : |(218110947/400000000 : ℝ)|=(218110947/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_6 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278813029/10000000000 : ℝ)*x 0 + (2726386851/5000000000 : ℝ)*x 1 + (-153716669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278813029/10000000000 : ℝ)^4819 ≤ (44429210805441/100000000000000 : ℝ)^3795 := by
    have hnat : (5278813029 : ℕ)^4819*100000000000000^3795 ≤ 44429210805441^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278813029 10000000000 44429210805441 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726386851/5000000000 : ℝ)^4819 ≤ (46296621967279/100000000000000 : ℝ)^3795 := by
    have hnat : (2726386851 : ℕ)^4819*100000000000000^3795 ≤ 46296621967279^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726386851 5000000000 46296621967279 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153716669/1000000000 : ℝ)^4819 ≤ (9274167217497/100000000000000 : ℝ)^3795 := by
    have hnat : (153716669 : ℕ)^4819*100000000000000^3795 ≤ 9274167217497^3795*1000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153716669 1000000000 9274167217497 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278813029/10000000000 : ℝ), (2726386851/5000000000 : ℝ), (-153716669/1000000000 : ℝ)] ![(44429210805441/100000000000000 : ℝ), (46296621967279/100000000000000 : ℝ), (9274167217497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278813029/10000000000 : ℝ)|^4819 ≤ (44429210805441/100000000000000 : ℝ)^3795
        have hw : |(5278813029/10000000000 : ℝ)|=(5278813029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726386851/5000000000 : ℝ)|^4819 ≤ (46296621967279/100000000000000 : ℝ)^3795
        have hw : |(2726386851/5000000000 : ℝ)|=(2726386851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153716669/1000000000 : ℝ)|^4819 ≤ (9274167217497/100000000000000 : ℝ)^3795
        have hw : |(-153716669/1000000000 : ℝ)|=(153716669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_s4_7 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84010443/200000000 : ℝ)*x 0 + (454729781/1000000000 : ℝ)*x 1 + (968592727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84010443/200000000 : ℝ)^4819 ≤ (33239898148949/100000000000000 : ℝ)^3795 := by
    have hnat : (84010443 : ℕ)^4819*100000000000000^3795 ≤ 33239898148949^3795*200000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84010443 200000000 33239898148949 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454729781/1000000000 : ℝ)^4819 ≤ (4595316700671/12500000000000 : ℝ)^3795 := by
    have hnat : (454729781 : ℕ)^4819*12500000000000^3795 ≤ 4595316700671^3795*1000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454729781 1000000000 4595316700671 12500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968592727/2500000000 : ℝ)^4819 ≤ (7499392056057/25000000000000 : ℝ)^3795 := by
    have hnat : (968592727 : ℕ)^4819*25000000000000^3795 ≤ 7499392056057^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968592727 2500000000 7499392056057 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84010443/200000000 : ℝ), (454729781/1000000000 : ℝ), (968592727/2500000000 : ℝ)] ![(33239898148949/100000000000000 : ℝ), (4595316700671/12500000000000 : ℝ), (7499392056057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84010443/200000000 : ℝ)|^4819 ≤ (33239898148949/100000000000000 : ℝ)^3795
        have hw : |(84010443/200000000 : ℝ)|=(84010443/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454729781/1000000000 : ℝ)|^4819 ≤ (4595316700671/12500000000000 : ℝ)^3795
        have hw : |(454729781/1000000000 : ℝ)|=(454729781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968592727/2500000000 : ℝ)|^4819 ≤ (7499392056057/25000000000000 : ℝ)^3795
        have hw : |(968592727/2500000000 : ℝ)|=(968592727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1625_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4081/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1053/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3263/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4081/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5261/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4081/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5261/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4081/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5261/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4081/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5261/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4081/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5261/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4081/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5261/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5261/50000 : ℝ) ^ (4815/1024 : ℝ) ≤ (2522092655115511/100000000000000000000 : ℝ) := by
    have hpowers : (5261/50000 : ℝ)^4815 ≤ (2522092655115511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5261 : ℕ)^4815*100000000000000000000^1024 ≤ 2522092655115511^1024*50000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5261 50000 2522092655115511 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5261/50000 : ℝ)) (X := (2522092655115511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4081/25000 : ℝ) ^ (4815/1024 : ℝ) ≤ (19888121376723597/100000000000000000000 : ℝ) := by
    have hpowers : (4081/25000 : ℝ)^4815 ≤ (19888121376723597/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4081 : ℕ)^4815*100000000000000000000^1024 ≤ 19888121376723597^1024*25000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4081 25000 19888121376723597 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4081/25000 : ℝ)) (X := (19888121376723597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002522092655115511/50000000000000000000 : ℝ) ≤ (2000021454385019/2000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50002522092655115511/50000000000000000000 : ℝ)^1024 ≤ (2000021454385019/2000000000000000 : ℝ)^4815 := by
      have hnat : (50002522092655115511 : ℕ)^1024*2000000000000000^4815 ≤ 2000021454385019^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002522092655115511 50000000000000000000 2000021454385019 2000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000021454385019/2000000000000000 : ℝ)) (X := (50002522092655115511/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005602553507959777/25000000000000000000 : ℝ) ≤ (5000238276582877/5000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (25005602553507959777/25000000000000000000 : ℝ)^1024 ≤ (5000238276582877/5000000000000000 : ℝ)^4815 := by
      have hnat : (25005602553507959777 : ℕ)^1024*5000000000000000^4815 ≤ 5000238276582877^4815*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005602553507959777 25000000000000000000 5000238276582877 5000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000238276582877/5000000000000000 : ℝ)) (X := (25005602553507959777/25000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019888121376723597/50000000000000000000 : ℝ) ≤ (10000845834406413/10000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50019888121376723597/50000000000000000000 : ℝ)^1024 ≤ (10000845834406413/10000000000000000 : ℝ)^4815 := by
      have hnat : (50019888121376723597 : ℕ)^1024*10000000000000000^4815 ≤ 10000845834406413^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019888121376723597 50000000000000000000 10000845834406413 10000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000845834406413/10000000000000000 : ℝ)) (X := (50019888121376723597/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2522092655115511/100000000000000000000 : ℝ) ≤ ((29006425618640486597/29010000000000000000 : ℝ)+2*(369281240659/580200000000000 : ℝ)*(5261/50000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (29006425618640486597/29010000000000000000 : ℝ)+2*(369281240659/580200000000000 : ℝ)*(5261/50000 : ℝ)=(2000021454385019/2000000000000000 : ℝ) by norm_num, show 1+2*(2522092655115511/100000000000000000000 : ℝ)=(50002522092655115511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19888121376723597/100000000000000000000 : ℝ)+(2522092655115511/100000000000000000000 : ℝ) ≤ ((29006425618640486597/29010000000000000000 : ℝ)+(369281240659/580200000000000 : ℝ)*((4081/25000 : ℝ)+(5261/50000 : ℝ)))^(4815/1024 : ℝ) := by
    rw [show (29006425618640486597/29010000000000000000 : ℝ)+(369281240659/580200000000000 : ℝ)*((4081/25000 : ℝ)+(5261/50000 : ℝ))=(5000238276582877/5000000000000000 : ℝ) by norm_num, show 1+(19888121376723597/100000000000000000000 : ℝ)+(2522092655115511/100000000000000000000 : ℝ)=(25005602553507959777/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19888121376723597/100000000000000000000 : ℝ) ≤ ((29006425618640486597/29010000000000000000 : ℝ)+2*(369281240659/580200000000000 : ℝ)*(4081/25000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (29006425618640486597/29010000000000000000 : ℝ)+2*(369281240659/580200000000000 : ℝ)*(4081/25000 : ℝ)=(10000845834406413/10000000000000000 : ℝ) by norm_num, show 1+2*(19888121376723597/100000000000000000000 : ℝ)=(50019888121376723597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29006425618640486597/29010000000000000000 : ℝ)*(X 1 0+X 2 0)+(369281240659/580200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (4081/25000 : ℝ)) (c := (29006425618640486597/29010000000000000000 : ℝ)) (alpha := (369281240659/580200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29006425618640486597/29010000000000000000 : ℝ)*(X 0 1+X 2 1)+(369281240659/580200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (4081/25000 : ℝ)) (c := (29006425618640486597/29010000000000000000 : ℝ)) (alpha := (369281240659/580200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29006425618640486597/29010000000000000000 : ℝ)*(X 0 2+X 1 2)+(369281240659/580200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (5261/50000 : ℝ)) (hi := (4081/25000 : ℝ)) (c := (29006425618640486597/29010000000000000000 : ℝ)) (alpha := (369281240659/580200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-833624883/5000000000 : ℝ)*X 0 0+(218193347/400000000 : ℝ)*X 0 1+(5182203137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337849849/2500000000 : ℝ)*X 1 0+(-903868803/5000000000 : ℝ)*X 1 1+(323887667/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351399027/10000000000 : ℝ)*X 2 0+(2591101563/5000000000 : ℝ)*X 2 1+(-903868749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2100176149/5000000000 : ℝ)*X 0 0+(3869207823/10000000000 : ℝ)*X 0 1+(36419257/80000000 : ℝ)*X 0 2+(2100176149/5000000000 : ℝ)*X 1 0+(3869207823/10000000000 : ℝ)*X 1 1+(36419257/80000000 : ℝ)*X 1 2+(2100176149/5000000000 : ℝ)*X 2 0+(3869207823/10000000000 : ℝ)*X 2 1+(36419257/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-416829417/2500000000 : ℝ)*X 0 0+(1036848323/2000000000 : ℝ)*X 0 1+(5452773677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278813021/10000000000 : ℝ)*X 1 0+(-1537166737/10000000000 : ℝ)*X 1 1+(218110947/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278813029/10000000000 : ℝ)*X 2 0+(2726386851/5000000000 : ℝ)*X 2 1+(-153716669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((84010443/200000000 : ℝ)*X 0 0+(454729781/1000000000 : ℝ)*X 0 1+(968592727/2500000000 : ℝ)*X 0 2+(84010443/200000000 : ℝ)*X 1 0+(454729781/1000000000 : ℝ)*X 1 1+(968592727/2500000000 : ℝ)*X 1 2+(84010443/200000000 : ℝ)*X 2 0+(454729781/1000000000 : ℝ)*X 2 1+(968592727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172299881877561180228645319/60437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25438609/5000000000000 : ℝ)*(base19) + (40074323/25000000000000 : ℝ)*(base23) + (25567381/50000000000000 : ℝ)*(lower2) + (60452701/100000000000000 : ℝ)*(upper3) + (932807/2500000000000 : ℝ)*(upper5) + (641459529019873/25000000000000 : ℝ)*(major0) + (641459529019873/25000000000000 : ℝ)*(major1) + (641459529019873/25000000000000 : ℝ)*(major2) + (3667968984996127/100000000000000 : ℝ)*(sp0) + (1833984498725009/50000000000000 : ℝ)*(sp1) + (733593869184981/20000000000000 : ℝ)*(sp2) + (731852081732849/50000000000000 : ℝ)*(sp3) + (52122607/10000000000000 : ℝ)*(sp4) + (1233720923/50000000000000 : ℝ)*(sp7) + (182963328863443/12500000000000 : ℝ)*(f.failure) + (1833984753111099/50000000000000 : ℝ)*(f.sum) + (2022723045269/906562500000000000000000000 : ℝ)*base65 + (7425678203371242181/725250000000000000000000000000000 : ℝ)*base67 + (6368313224891742181/725250000000000000000000000000000 : ℝ)*base69 + (2880710844810492181/725250000000000000000000000000000 : ℝ)*base71 + (320500545823/1813125000000000000000000000 : ℝ)*base73 + (2791642542739992181/725250000000000000000000000000000 : ℝ)*base75 + (9287077402658742181/725250000000000000000000000000000 : ℝ)*base77 + (1154880199817507819/725250000000000000000000000000000 : ℝ)*base80 + (19489091978513/7252500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1711621/625000000000000000000 : ℝ)*base89 + (1711621/625000000000000000000 : ℝ)*base91 + (1711621/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (635369252859942583960916163/120875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162734517/20000000000000 : ℝ)*(base19) + (437463493/50000000000000 : ℝ)*(base23) + (963919/390625000000 : ℝ)*(lower1) + (4899491/4000000000000 : ℝ)*(upper3) + (19421873/100000000000000 : ℝ)*(lower4) + (21802101/20000000000000 : ℝ)*(upper5) + (1302495611399921/50000000000000 : ℝ)*(major0) + (1302495611399921/50000000000000 : ℝ)*(major1) + (1302495611399921/50000000000000 : ℝ)*(major2) + (342147193/25000000000000 : ℝ)*(sp2) + (186197018964429/5000000000000 : ℝ)*(sp4) + (930984891403999/25000000000000 : ℝ)*(sp5) + (1861969067886411/50000000000000 : ℝ)*(sp6) + (1486041891097213/100000000000000 : ℝ)*(sp7) + (1486041891097213/100000000000000 : ℝ)*(f.failure) + (186197018964429/5000000000000 : ℝ)*(f.sum) + (6505310489611/14505000000000000000000000000 : ℝ)*base66 + (48420090413589308837/1450500000000000000000000000000000 : ℝ)*base67 + (5377767990372308837/1450500000000000000000000000000000 : ℝ)*base69 + (145648568045571308837/1450500000000000000000000000000000 : ℝ)*base71 + (38452328264549/14505000000000000000000000000 : ℝ)*base73 + (187737445635947691163/1450500000000000000000000000000000 : ℝ)*base76 + (10707191365488308837/1450500000000000000000000000000000 : ℝ)*base77 + (3186869284581308837/1450500000000000000000000000000000 : ℝ)*base79 + (65541694086901/14505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (35079189/5000000000000000000000 : ℝ)*base90 + (35079189/5000000000000000000000 : ℝ)*base92 + (35079189/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1625_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4081/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1053/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3263/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1625_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1625_box_0 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-279988361/2000000000 : ℝ)*x 0 + (2707144969/5000000000 : ℝ)*x 1 + (5414288367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279988361/2000000000 : ℝ)^4819 ≤ (4117901317207/50000000000000 : ℝ)^3795 := by
    have hnat : (279988361 : ℕ)^4819*50000000000000^3795 ≤ 4117901317207^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279988361 2000000000 4117901317207 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707144969/5000000000 : ℝ)^4819 ≤ (22941053564027/50000000000000 : ℝ)^3795 := by
    have hnat : (2707144969 : ℕ)^4819*50000000000000^3795 ≤ 22941053564027^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707144969 5000000000 22941053564027 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414288367/10000000000 : ℝ)^4819 ≤ (45882090222743/100000000000000 : ℝ)^3795 := by
    have hnat : (5414288367 : ℕ)^4819*100000000000000^3795 ≤ 45882090222743^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414288367 10000000000 45882090222743 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-279988361/2000000000 : ℝ), (2707144969/5000000000 : ℝ), (5414288367/10000000000 : ℝ)] ![(4117901317207/50000000000000 : ℝ), (22941053564027/50000000000000 : ℝ), (45882090222743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-279988361/2000000000 : ℝ)|^4819 ≤ (4117901317207/50000000000000 : ℝ)^3795
        have hw : |(-279988361/2000000000 : ℝ)|=(279988361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707144969/5000000000 : ℝ)|^4819 ≤ (22941053564027/50000000000000 : ℝ)^3795
        have hw : |(2707144969/5000000000 : ℝ)|=(2707144969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414288367/10000000000 : ℝ)|^4819 ≤ (45882090222743/100000000000000 : ℝ)^3795
        have hw : |(5414288367/10000000000 : ℝ)|=(5414288367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_1 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251253911/10000000000 : ℝ)*x 0 + (-1628963669/10000000000 : ℝ)*x 1 + (1353572053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251253911/10000000000 : ℝ)^4819 ≤ (22067439773471/50000000000000 : ℝ)^3795 := by
    have hnat : (5251253911 : ℕ)^4819*50000000000000^3795 ≤ 22067439773471^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251253911 10000000000 22067439773471 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1628963669/10000000000 : ℝ)^4819 ≤ (9983031881443/100000000000000 : ℝ)^3795 := by
    have hnat : (1628963669 : ℕ)^4819*100000000000000^3795 ≤ 9983031881443^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628963669 10000000000 9983031881443 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353572053/2500000000 : ℝ)^4819 ≤ (4588208855481/10000000000000 : ℝ)^3795 := by
    have hnat : (1353572053 : ℕ)^4819*10000000000000^3795 ≤ 4588208855481^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353572053 2500000000 4588208855481 10000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251253911/10000000000 : ℝ), (-1628963669/10000000000 : ℝ), (1353572053/2500000000 : ℝ)] ![(22067439773471/50000000000000 : ℝ), (9983031881443/100000000000000 : ℝ), (4588208855481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251253911/10000000000 : ℝ)|^4819 ≤ (22067439773471/50000000000000 : ℝ)^3795
        have hw : |(5251253911/10000000000 : ℝ)|=(5251253911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1628963669/10000000000 : ℝ)|^4819 ≤ (9983031881443/100000000000000 : ℝ)^3795
        have hw : |(-1628963669/10000000000 : ℝ)|=(1628963669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353572053/2500000000 : ℝ)|^4819 ≤ (4588208855481/10000000000000 : ℝ)^3795
        have hw : |(1353572053/2500000000 : ℝ)|=(1353572053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_2 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625626417/5000000000 : ℝ)*x 0 + (5414289481/10000000000 : ℝ)*x 1 + (-25452553/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625626417/5000000000 : ℝ)^4819 ≤ (8826973610543/20000000000000 : ℝ)^3795 := by
    have hnat : (2625626417 : ℕ)^4819*20000000000000^3795 ≤ 8826973610543^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625626417 5000000000 8826973610543 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414289481/10000000000 : ℝ)^4819 ≤ (2294105110517/5000000000000 : ℝ)^3795 := by
    have hnat : (5414289481 : ℕ)^4819*5000000000000^3795 ≤ 2294105110517^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414289481 10000000000 2294105110517 5000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25452553/156250000 : ℝ)^4819 ≤ (2495757431451/25000000000000 : ℝ)^3795 := by
    have hnat : (25452553 : ℕ)^4819*25000000000000^3795 ≤ 2495757431451^3795*156250000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25452553 156250000 2495757431451 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625626417/5000000000 : ℝ), (5414289481/10000000000 : ℝ), (-25452553/156250000 : ℝ)] ![(8826973610543/20000000000000 : ℝ), (2294105110517/5000000000000 : ℝ), (2495757431451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625626417/5000000000 : ℝ)|^4819 ≤ (8826973610543/20000000000000 : ℝ)^3795
        have hw : |(2625626417/5000000000 : ℝ)|=(2625626417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414289481/10000000000 : ℝ)|^4819 ≤ (2294105110517/5000000000000 : ℝ)^3795
        have hw : |(5414289481/10000000000 : ℝ)|=(5414289481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25452553/156250000 : ℝ)|^4819 ≤ (2495757431451/25000000000000 : ℝ)^3795
        have hw : |(-25452553/156250000 : ℝ)|=(25452553/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_3 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4478967479/10000000000 : ℝ)*x 0 + (50918747/125000000 : ℝ)*x 1 + (4073499137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478967479/10000000000 : ℝ)^4819 ≤ (9015622086057/25000000000000 : ℝ)^3795 := by
    have hnat : (4478967479 : ℕ)^4819*25000000000000^3795 ≤ 9015622086057^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478967479 10000000000 9015622086057 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50918747/125000000 : ℝ)^4819 ≤ (15984379463941/50000000000000 : ℝ)^3795 := by
    have hnat : (50918747 : ℕ)^4819*50000000000000^3795 ≤ 15984379463941^3795*125000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50918747 125000000 15984379463941 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4073499137/10000000000 : ℝ)^4819 ≤ (31968752719317/100000000000000 : ℝ)^3795 := by
    have hnat : (4073499137 : ℕ)^4819*100000000000000^3795 ≤ 31968752719317^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4073499137 10000000000 31968752719317 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478967479/10000000000 : ℝ), (50918747/125000000 : ℝ), (4073499137/10000000000 : ℝ)] ![(9015622086057/25000000000000 : ℝ), (15984379463941/50000000000000 : ℝ), (31968752719317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478967479/10000000000 : ℝ)|^4819 ≤ (9015622086057/25000000000000 : ℝ)^3795
        have hw : |(4478967479/10000000000 : ℝ)|=(4478967479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50918747/125000000 : ℝ)|^4819 ≤ (15984379463941/50000000000000 : ℝ)^3795
        have hw : |(50918747/125000000 : ℝ)|=(50918747/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4073499137/10000000000 : ℝ)|^4819 ≤ (31968752719317/100000000000000 : ℝ)^3795
        have hw : |(4073499137/10000000000 : ℝ)|=(4073499137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_4 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-486314941/2500000000 : ℝ)*x 0 + (5214869311/10000000000 : ℝ)*x 1 + (1042973819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486314941/2500000000 : ℝ)^4819 ≤ (6253070768011/50000000000000 : ℝ)^3795 := by
    have hnat : (486314941 : ℕ)^4819*50000000000000^3795 ≤ 6253070768011^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486314941 2500000000 6253070768011 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214869311/10000000000 : ℝ)^4819 ≤ (43746930375751/100000000000000 : ℝ)^3795 := by
    have hnat : (5214869311 : ℕ)^4819*100000000000000^3795 ≤ 43746930375751^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214869311 10000000000 43746930375751 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042973819/2000000000 : ℝ)^4819 ≤ (43746928074823/100000000000000 : ℝ)^3795 := by
    have hnat : (1042973819 : ℕ)^4819*100000000000000^3795 ≤ 43746928074823^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042973819 2000000000 43746928074823 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486314941/2500000000 : ℝ), (5214869311/10000000000 : ℝ), (1042973819/2000000000 : ℝ)] ![(6253070768011/50000000000000 : ℝ), (43746930375751/100000000000000 : ℝ), (43746928074823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486314941/2500000000 : ℝ)|^4819 ≤ (6253070768011/50000000000000 : ℝ)^3795
        have hw : |(-486314941/2500000000 : ℝ)|=(486314941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214869311/10000000000 : ℝ)|^4819 ≤ (43746930375751/100000000000000 : ℝ)^3795
        have hw : |(5214869311/10000000000 : ℝ)|=(5214869311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042973819/2000000000 : ℝ)|^4819 ≤ (43746928074823/100000000000000 : ℝ)^3795
        have hw : |(1042973819/2000000000 : ℝ)|=(1042973819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_5 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347149633/2500000000 : ℝ)*x 0 + (-1713727931/10000000000 : ℝ)*x 1 + (5214869163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347149633/2500000000 : ℝ)^4819 ≤ (45605822689101/100000000000000 : ℝ)^3795 := by
    have hnat : (1347149633 : ℕ)^4819*100000000000000^3795 ≤ 45605822689101^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347149633 2500000000 45605822689101 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713727931/10000000000 : ℝ)^4819 ≤ (5323624249027/50000000000000 : ℝ)^3795 := by
    have hnat : (1713727931 : ℕ)^4819*50000000000000^3795 ≤ 5323624249027^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713727931 10000000000 5323624249027 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214869163/10000000000 : ℝ)^4819 ≤ (4374692879919/10000000000000 : ℝ)^3795 := by
    have hnat : (5214869163 : ℕ)^4819*10000000000000^3795 ≤ 4374692879919^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214869163 10000000000 4374692879919 10000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347149633/2500000000 : ℝ), (-1713727931/10000000000 : ℝ), (5214869163/10000000000 : ℝ)] ![(45605822689101/100000000000000 : ℝ), (5323624249027/50000000000000 : ℝ), (4374692879919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347149633/2500000000 : ℝ)|^4819 ≤ (45605822689101/100000000000000 : ℝ)^3795
        have hw : |(1347149633/2500000000 : ℝ)|=(1347149633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713727931/10000000000 : ℝ)|^4819 ≤ (5323624249027/50000000000000 : ℝ)^3795
        have hw : |(-1713727931/10000000000 : ℝ)|=(1713727931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214869163/10000000000 : ℝ)|^4819 ≤ (4374692879919/10000000000000 : ℝ)^3795
        have hw : |(5214869163/10000000000 : ℝ)|=(5214869163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_6 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077719691/2000000000 : ℝ)*x 0 + (5214869231/10000000000 : ℝ)*x 1 + (-342745589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077719691/2000000000 : ℝ)^4819 ≤ (22802910930789/50000000000000 : ℝ)^3795 := by
    have hnat : (1077719691 : ℕ)^4819*50000000000000^3795 ≤ 22802910930789^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077719691 2000000000 22802910930789 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214869231/10000000000 : ℝ)^4819 ≤ (10936732380889/25000000000000 : ℝ)^3795 := by
    have hnat : (5214869231 : ℕ)^4819*25000000000000^3795 ≤ 10936732380889^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214869231 10000000000 10936732380889 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342745589/2000000000 : ℝ)^4819 ≤ (2129449721701/20000000000000 : ℝ)^3795 := by
    have hnat : (342745589 : ℕ)^4819*20000000000000^3795 ≤ 2129449721701^3795*2000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342745589 2000000000 2129449721701 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077719691/2000000000 : ℝ), (5214869231/10000000000 : ℝ), (-342745589/2000000000 : ℝ)] ![(22802910930789/50000000000000 : ℝ), (10936732380889/25000000000000 : ℝ), (2129449721701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077719691/2000000000 : ℝ)|^4819 ≤ (22802910930789/50000000000000 : ℝ)^3795
        have hw : |(1077719691/2000000000 : ℝ)|=(1077719691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214869231/10000000000 : ℝ)|^4819 ≤ (10936732380889/25000000000000 : ℝ)^3795
        have hw : |(5214869231/10000000000 : ℝ)|=(5214869231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342745589/2000000000 : ℝ)|^4819 ≤ (2129449721701/20000000000000 : ℝ)^3795
        have hw : |(-342745589/2000000000 : ℝ)|=(342745589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_7 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1957812109/5000000000 : ℝ)*x 0 + (1088708771/2500000000 : ℝ)*x 1 + (4354834913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1957812109/5000000000 : ℝ)^4819 ≤ (6080748165213/20000000000000 : ℝ)^3795 := by
    have hnat : (1957812109 : ℕ)^4819*20000000000000^3795 ≤ 6080748165213^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957812109 5000000000 6080748165213 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088708771/2500000000 : ℝ)^4819 ≤ (34798130447621/100000000000000 : ℝ)^3795 := by
    have hnat : (1088708771 : ℕ)^4819*100000000000000^3795 ≤ 34798130447621^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088708771 2500000000 34798130447621 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4354834913/10000000000 : ℝ)^4819 ≤ (17399064356259/50000000000000 : ℝ)^3795 := by
    have hnat : (4354834913 : ℕ)^4819*50000000000000^3795 ≤ 17399064356259^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354834913 10000000000 17399064356259 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1957812109/5000000000 : ℝ), (1088708771/2500000000 : ℝ), (4354834913/10000000000 : ℝ)] ![(6080748165213/20000000000000 : ℝ), (34798130447621/100000000000000 : ℝ), (17399064356259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1957812109/5000000000 : ℝ)|^4819 ≤ (6080748165213/20000000000000 : ℝ)^3795
        have hw : |(1957812109/5000000000 : ℝ)|=(1957812109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088708771/2500000000 : ℝ)|^4819 ≤ (34798130447621/100000000000000 : ℝ)^3795
        have hw : |(1088708771/2500000000 : ℝ)|=(1088708771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4354834913/10000000000 : ℝ)|^4819 ≤ (17399064356259/50000000000000 : ℝ)^3795
        have hw : |(4354834913/10000000000 : ℝ)|=(4354834913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_8 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1829163621/10000000000 : ℝ)*x 0 + (1268013937/2500000000 : ℝ)*x 1 + (5444052967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1829163621/10000000000 : ℝ)^4819 ≤ (5783052162433/50000000000000 : ℝ)^3795 := by
    have hnat : (1829163621 : ℕ)^4819*50000000000000^3795 ≤ 5783052162433^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829163621 10000000000 5783052162433 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268013937/2500000000 : ℝ)^4819 ≤ (8446255104909/20000000000000 : ℝ)^3795 := by
    have hnat : (1268013937 : ℕ)^4819*20000000000000^3795 ≤ 8446255104909^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268013937 2500000000 8446255104909 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444052967/10000000000 : ℝ)^4819 ≤ (46202620136837/100000000000000 : ℝ)^3795 := by
    have hnat : (5444052967 : ℕ)^4819*100000000000000^3795 ≤ 46202620136837^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444052967 10000000000 46202620136837 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1829163621/10000000000 : ℝ), (1268013937/2500000000 : ℝ), (5444052967/10000000000 : ℝ)] ![(5783052162433/50000000000000 : ℝ), (8446255104909/20000000000000 : ℝ), (46202620136837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1829163621/10000000000 : ℝ)|^4819 ≤ (5783052162433/50000000000000 : ℝ)^3795
        have hw : |(-1829163621/10000000000 : ℝ)|=(1829163621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268013937/2500000000 : ℝ)|^4819 ≤ (8446255104909/20000000000000 : ℝ)^3795
        have hw : |(1268013937/2500000000 : ℝ)|=(1268013937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444052967/10000000000 : ℝ)|^4819 ≤ (46202620136837/100000000000000 : ℝ)^3795
        have hw : |(5444052967/10000000000 : ℝ)|=(5444052967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_9 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230751983/10000000000 : ℝ)*x 0 + (-1615863261/10000000000 : ℝ)*x 1 + (5444052647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230751983/10000000000 : ℝ)^4819 ≤ (43916189134973/100000000000000 : ℝ)^3795 := by
    have hnat : (5230751983 : ℕ)^4819*100000000000000^3795 ≤ 43916189134973^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230751983 10000000000 43916189134973 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615863261/10000000000 : ℝ)^4819 ≤ (4940597084713/50000000000000 : ℝ)^3795 := by
    have hnat : (1615863261 : ℕ)^4819*50000000000000^3795 ≤ 4940597084713^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615863261 10000000000 4940597084713 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444052647/10000000000 : ℝ)^4819 ≤ (5775327086033/12500000000000 : ℝ)^3795 := by
    have hnat : (5444052647 : ℕ)^4819*12500000000000^3795 ≤ 5775327086033^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444052647 10000000000 5775327086033 12500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230751983/10000000000 : ℝ), (-1615863261/10000000000 : ℝ), (5444052647/10000000000 : ℝ)] ![(43916189134973/100000000000000 : ℝ), (4940597084713/50000000000000 : ℝ), (5775327086033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230751983/10000000000 : ℝ)|^4819 ≤ (43916189134973/100000000000000 : ℝ)^3795
        have hw : |(5230751983/10000000000 : ℝ)|=(5230751983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1615863261/10000000000 : ℝ)|^4819 ≤ (4940597084713/50000000000000 : ℝ)^3795
        have hw : |(-1615863261/10000000000 : ℝ)|=(1615863261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444052647/10000000000 : ℝ)|^4819 ≤ (5775327086033/12500000000000 : ℝ)^3795
        have hw : |(5444052647/10000000000 : ℝ)|=(5444052647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_10 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230751783/10000000000 : ℝ)*x 0 + (2722026371/5000000000 : ℝ)*x 1 + (-403965851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230751783/10000000000 : ℝ)^4819 ≤ (8783237400547/20000000000000 : ℝ)^3795 := by
    have hnat : (5230751783 : ℕ)^4819*20000000000000^3795 ≤ 8783237400547^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230751783 10000000000 8783237400547 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722026371/5000000000 : ℝ)^4819 ≤ (46202617712059/100000000000000 : ℝ)^3795 := by
    have hnat : (2722026371 : ℕ)^4819*100000000000000^3795 ≤ 46202617712059^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722026371 5000000000 46202617712059 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403965851/2500000000 : ℝ)^4819 ≤ (9881195279843/100000000000000 : ℝ)^3795 := by
    have hnat : (403965851 : ℕ)^4819*100000000000000^3795 ≤ 9881195279843^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403965851 2500000000 9881195279843 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230751783/10000000000 : ℝ), (2722026371/5000000000 : ℝ), (-403965851/2500000000 : ℝ)] ![(8783237400547/20000000000000 : ℝ), (46202617712059/100000000000000 : ℝ), (9881195279843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230751783/10000000000 : ℝ)|^4819 ≤ (8783237400547/20000000000000 : ℝ)^3795
        have hw : |(5230751783/10000000000 : ℝ)|=(5230751783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722026371/5000000000 : ℝ)|^4819 ≤ (46202617712059/100000000000000 : ℝ)^3795
        have hw : |(2722026371/5000000000 : ℝ)|=(2722026371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403965851/2500000000 : ℝ)|^4819 ≤ (9881195279843/100000000000000 : ℝ)^3795
        have hw : |(-403965851/2500000000 : ℝ)|=(403965851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_11 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1140164111/2500000000 : ℝ)*x 0 + (4031434273/10000000000 : ℝ)*x 1 + (2015717133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1140164111/2500000000 : ℝ)^4819 ≤ (36899726369061/100000000000000 : ℝ)^3795 := by
    have hnat : (1140164111 : ℕ)^4819*100000000000000^3795 ≤ 36899726369061^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140164111 2500000000 36899726369061 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031434273/10000000000 : ℝ)^4819 ≤ (31550136845131/100000000000000 : ℝ)^3795 := by
    have hnat : (4031434273 : ℕ)^4819*100000000000000^3795 ≤ 31550136845131^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031434273 10000000000 31550136845131 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015717133/5000000000 : ℝ)^4819 ≤ (31550136775567/100000000000000 : ℝ)^3795 := by
    have hnat : (2015717133 : ℕ)^4819*100000000000000^3795 ≤ 31550136775567^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015717133 5000000000 31550136775567 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1140164111/2500000000 : ℝ), (4031434273/10000000000 : ℝ), (2015717133/5000000000 : ℝ)] ![(36899726369061/100000000000000 : ℝ), (31550136845131/100000000000000 : ℝ), (31550136775567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1140164111/2500000000 : ℝ)|^4819 ≤ (36899726369061/100000000000000 : ℝ)^3795
        have hw : |(1140164111/2500000000 : ℝ)|=(1140164111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031434273/10000000000 : ℝ)|^4819 ≤ (31550136845131/100000000000000 : ℝ)^3795
        have hw : |(4031434273/10000000000 : ℝ)|=(4031434273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015717133/5000000000 : ℝ)|^4819 ≤ (31550136775567/100000000000000 : ℝ)^3795
        have hw : |(2015717133/5000000000 : ℝ)|=(2015717133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_12 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-378649623/2500000000 : ℝ)*x 0 + (693929343/1250000000 : ℝ)*x 1 + (2597504279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378649623/2500000000 : ℝ)^4819 ≤ (9101610529549/100000000000000 : ℝ)^3795 := by
    have hnat : (378649623 : ℕ)^4819*100000000000000^3795 ≤ 9101610529549^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378649623 2500000000 9101610529549 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693929343/1250000000 : ℝ)^4819 ≤ (9472583170517/20000000000000 : ℝ)^3795 := by
    have hnat : (693929343 : ℕ)^4819*20000000000000^3795 ≤ 9472583170517^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693929343 1250000000 9472583170517 20000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597504279/5000000000 : ℝ)^4819 ≤ (10883868400881/25000000000000 : ℝ)^3795 := by
    have hnat : (2597504279 : ℕ)^4819*25000000000000^3795 ≤ 10883868400881^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597504279 5000000000 10883868400881 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378649623/2500000000 : ℝ), (693929343/1250000000 : ℝ), (2597504279/5000000000 : ℝ)] ![(9101610529549/100000000000000 : ℝ), (9472583170517/20000000000000 : ℝ), (10883868400881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378649623/2500000000 : ℝ)|^4819 ≤ (9101610529549/100000000000000 : ℝ)^3795
        have hw : |(-378649623/2500000000 : ℝ)|=(378649623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(693929343/1250000000 : ℝ)|^4819 ≤ (9472583170517/20000000000000 : ℝ)^3795
        have hw : |(693929343/1250000000 : ℝ)|=(693929343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597504279/5000000000 : ℝ)|^4819 ≤ (10883868400881/25000000000000 : ℝ)^3795
        have hw : |(2597504279/5000000000 : ℝ)|=(2597504279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_13 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350571381/2500000000 : ℝ)*x 0 + (-860937367/5000000000 : ℝ)*x 1 + (5195008167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350571381/2500000000 : ℝ)^4819 ≤ (22876483984031/50000000000000 : ℝ)^3795 := by
    have hnat : (1350571381 : ℕ)^4819*50000000000000^3795 ≤ 22876483984031^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350571381 2500000000 22876483984031 50000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860937367/5000000000 : ℝ)^4819 ≤ (10711562569737/100000000000000 : ℝ)^3795 := by
    have hnat : (860937367 : ℕ)^4819*100000000000000^3795 ≤ 10711562569737^3795*5000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860937367 5000000000 10711562569737 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195008167/10000000000 : ℝ)^4819 ≤ (2720966840169/6250000000000 : ℝ)^3795 := by
    have hnat : (5195008167 : ℕ)^4819*6250000000000^3795 ≤ 2720966840169^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195008167 10000000000 2720966840169 6250000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350571381/2500000000 : ℝ), (-860937367/5000000000 : ℝ), (5195008167/10000000000 : ℝ)] ![(22876483984031/50000000000000 : ℝ), (10711562569737/100000000000000 : ℝ), (2720966840169/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350571381/2500000000 : ℝ)|^4819 ≤ (22876483984031/50000000000000 : ℝ)^3795
        have hw : |(1350571381/2500000000 : ℝ)|=(1350571381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-860937367/5000000000 : ℝ)|^4819 ≤ (10711562569737/100000000000000 : ℝ)^3795
        have hw : |(-860937367/5000000000 : ℝ)|=(860937367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195008167/10000000000 : ℝ)|^4819 ≤ (2720966840169/6250000000000 : ℝ)^3795
        have hw : |(5195008167/10000000000 : ℝ)|=(5195008167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_14 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350571339/2500000000 : ℝ)*x 0 + (5195007911/10000000000 : ℝ)*x 1 + (-1721875309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350571339/2500000000 : ℝ)^4819 ≤ (1143824154033/2500000000000 : ℝ)^3795 := by
    have hnat : (1350571339 : ℕ)^4819*2500000000000^3795 ≤ 1143824154033^3795*2500000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350571339 2500000000 1143824154033 2500000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195007911/10000000000 : ℝ)^4819 ≤ (10883866679621/25000000000000 : ℝ)^3795 := by
    have hnat : (5195007911 : ℕ)^4819*25000000000000^3795 ≤ 10883866679621^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195007911 10000000000 10883866679621 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1721875309/10000000000 : ℝ)^4819 ≤ (2677891777979/25000000000000 : ℝ)^3795 := by
    have hnat : (1721875309 : ℕ)^4819*25000000000000^3795 ≤ 2677891777979^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721875309 10000000000 2677891777979 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350571339/2500000000 : ℝ), (5195007911/10000000000 : ℝ), (-1721875309/10000000000 : ℝ)] ![(1143824154033/2500000000000 : ℝ), (10883866679621/25000000000000 : ℝ), (2677891777979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350571339/2500000000 : ℝ)|^4819 ≤ (1143824154033/2500000000000 : ℝ)^3795
        have hw : |(1350571339/2500000000 : ℝ)|=(1350571339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195007911/10000000000 : ℝ)|^4819 ≤ (10883866679621/25000000000000 : ℝ)^3795
        have hw : |(5195007911/10000000000 : ℝ)|=(5195007911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1721875309/10000000000 : ℝ)|^4819 ≤ (2677891777979/25000000000000 : ℝ)^3795
        have hw : |(-1721875309/10000000000 : ℝ)|=(1721875309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1625_box_15 (p : ℝ) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3857893389/10000000000 : ℝ)*x 0 + (547850473/1250000000 : ℝ)*x 1 + (4382804117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3857893389/10000000000 : ℝ)^4819 ≤ (29835658735883/100000000000000 : ℝ)^3795 := by
    have hnat : (3857893389 : ℕ)^4819*100000000000000^3795 ≤ 29835658735883^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857893389 10000000000 29835658735883 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547850473/1250000000 : ℝ)^4819 ≤ (35082168930323/100000000000000 : ℝ)^3795 := by
    have hnat : (547850473 : ℕ)^4819*100000000000000^3795 ≤ 35082168930323^3795*1250000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547850473 1250000000 35082168930323 100000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382804117/10000000000 : ℝ)^4819 ≤ (8770543078763/25000000000000 : ℝ)^3795 := by
    have hnat : (4382804117 : ℕ)^4819*25000000000000^3795 ≤ 8770543078763^3795*10000000000^4819 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382804117 10000000000 8770543078763 25000000000000 4819 3795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4819/1024 : ℝ)) 4819 3795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3857893389/10000000000 : ℝ), (547850473/1250000000 : ℝ), (4382804117/10000000000 : ℝ)] ![(29835658735883/100000000000000 : ℝ), (35082168930323/100000000000000 : ℝ), (8770543078763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3857893389/10000000000 : ℝ)|^4819 ≤ (29835658735883/100000000000000 : ℝ)^3795
        have hw : |(3857893389/10000000000 : ℝ)|=(3857893389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547850473/1250000000 : ℝ)|^4819 ≤ (35082168930323/100000000000000 : ℝ)^3795
        have hw : |(547850473/1250000000 : ℝ)|=(547850473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382804117/10000000000 : ℝ)|^4819 ≤ (8770543078763/25000000000000 : ℝ)^3795
        have hw : |(4382804117/10000000000 : ℝ)|=(4382804117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1625_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3263/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1053/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6497/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14589/25000 : ℝ) ∧ (10091/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87977/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3263/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1053/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3263/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1053/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3263/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1053/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3263/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1053/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3263/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1053/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3263/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1053/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1053/10000 : ℝ) ^ (4815/1024 : ℝ) ≤ (2531122083823097/100000000000000000000 : ℝ) := by
    have hpowers : (1053/10000 : ℝ)^4815 ≤ (2531122083823097/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1053 : ℕ)^4815*100000000000000000000^1024 ≤ 2531122083823097^1024*10000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1053 10000 2531122083823097 100000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1053/10000 : ℝ)) (X := (2531122083823097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3263/20000 : ℝ) ^ (4815/1024 : ℝ) ≤ (9918307393908607/50000000000000000000 : ℝ) := by
    have hpowers : (3263/20000 : ℝ)^4815 ≤ (9918307393908607/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3263 : ℕ)^4815*50000000000000000000^1024 ≤ 9918307393908607^1024*20000^4815 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3263 20000 9918307393908607 50000000000000000000 4815 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3263/20000 : ℝ)) (X := (9918307393908607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002531122083823097/50000000000000000000 : ℝ) ≤ (2500026913991317/2500000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (50002531122083823097/50000000000000000000 : ℝ)^1024 ≤ (2500026913991317/2500000000000000 : ℝ)^4815 := by
      have hnat : (50002531122083823097 : ℕ)^1024*2500000000000000^4815 ≤ 2500026913991317^4815*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002531122083823097 50000000000000000000 2500026913991317 2500000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500026913991317/2500000000000000 : ℝ)) (X := (50002531122083823097/50000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022367736871640311/100000000000000000000 : ℝ) ≤ (10000475649968533/10000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (100022367736871640311/100000000000000000000 : ℝ)^1024 ≤ (10000475649968533/10000000000000000 : ℝ)^4815 := by
      have hnat : (100022367736871640311 : ℕ)^1024*10000000000000000^4815 ≤ 10000475649968533^4815*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022367736871640311 100000000000000000000 10000475649968533 10000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000475649968533/10000000000000000 : ℝ)) (X := (100022367736871640311/100000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009918307393908607/25000000000000000000 : ℝ) ≤ (5000421821985899/5000000000000000 : ℝ) ^ (4815/1024 : ℝ) := by
    have hpowers : (25009918307393908607/25000000000000000000 : ℝ)^1024 ≤ (5000421821985899/5000000000000000 : ℝ)^4815 := by
      have hnat : (25009918307393908607 : ℕ)^1024*5000000000000000^4815 ≤ 5000421821985899^4815*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009918307393908607 25000000000000000000 5000421821985899 5000000000000000 1024 4815 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000421821985899/5000000000000000 : ℝ)) (X := (25009918307393908607/25000000000000000000 : ℝ)) (by norm_num) 4815 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2531122083823097/100000000000000000000 : ℝ) ≤ ((55618146957740687/55625000000000000 : ℝ)+2*(73598800653/115700000000000 : ℝ)*(1053/10000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (55618146957740687/55625000000000000 : ℝ)+2*(73598800653/115700000000000 : ℝ)*(1053/10000 : ℝ)=(2500026913991317/2500000000000000 : ℝ) by norm_num, show 1+2*(2531122083823097/100000000000000000000 : ℝ)=(50002531122083823097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9918307393908607/50000000000000000000 : ℝ)+(2531122083823097/100000000000000000000 : ℝ) ≤ ((55618146957740687/55625000000000000 : ℝ)+(73598800653/115700000000000 : ℝ)*((3263/20000 : ℝ)+(1053/10000 : ℝ)))^(4815/1024 : ℝ) := by
    rw [show (55618146957740687/55625000000000000 : ℝ)+(73598800653/115700000000000 : ℝ)*((3263/20000 : ℝ)+(1053/10000 : ℝ))=(10000475649968533/10000000000000000 : ℝ) by norm_num, show 1+(9918307393908607/50000000000000000000 : ℝ)+(2531122083823097/100000000000000000000 : ℝ)=(100022367736871640311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9918307393908607/50000000000000000000 : ℝ) ≤ ((55618146957740687/55625000000000000 : ℝ)+2*(73598800653/115700000000000 : ℝ)*(3263/20000 : ℝ))^(4815/1024 : ℝ) := by
    rw [show (55618146957740687/55625000000000000 : ℝ)+2*(73598800653/115700000000000 : ℝ)*(3263/20000 : ℝ)=(5000421821985899/5000000000000000 : ℝ) by norm_num, show 1+2*(9918307393908607/50000000000000000000 : ℝ)=(25009918307393908607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55618146957740687/55625000000000000 : ℝ)*(X 1 0+X 2 0)+(73598800653/115700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (1053/10000 : ℝ)) (hi := (3263/20000 : ℝ)) (c := (55618146957740687/55625000000000000 : ℝ)) (alpha := (73598800653/115700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55618146957740687/55625000000000000 : ℝ)*(X 0 1+X 2 1)+(73598800653/115700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (1053/10000 : ℝ)) (hi := (3263/20000 : ℝ)) (c := (55618146957740687/55625000000000000 : ℝ)) (alpha := (73598800653/115700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55618146957740687/55625000000000000 : ℝ)*(X 0 2+X 1 2)+(73598800653/115700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4815/1024 : ℝ)) (lo := (1053/10000 : ℝ)) (hi := (3263/20000 : ℝ)) (c := (55618146957740687/55625000000000000 : ℝ)) (alpha := (73598800653/115700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-279988361/2000000000 : ℝ)*X 0 0+(2707144969/5000000000 : ℝ)*X 0 1+(5414288367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251253911/10000000000 : ℝ)*X 1 0+(-1628963669/10000000000 : ℝ)*X 1 1+(1353572053/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625626417/5000000000 : ℝ)*X 2 0+(5414289481/10000000000 : ℝ)*X 2 1+(-25452553/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4478967479/10000000000 : ℝ)*X 0 0+(50918747/125000000 : ℝ)*X 0 1+(4073499137/10000000000 : ℝ)*X 0 2+(4478967479/10000000000 : ℝ)*X 1 0+(50918747/125000000 : ℝ)*X 1 1+(4073499137/10000000000 : ℝ)*X 1 2+(4478967479/10000000000 : ℝ)*X 2 0+(50918747/125000000 : ℝ)*X 2 1+(4073499137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-486314941/2500000000 : ℝ)*X 0 0+(5214869311/10000000000 : ℝ)*X 0 1+(1042973819/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1347149633/2500000000 : ℝ)*X 1 0+(-1713727931/10000000000 : ℝ)*X 1 1+(5214869163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1077719691/2000000000 : ℝ)*X 2 0+(5214869231/10000000000 : ℝ)*X 2 1+(-342745589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1957812109/5000000000 : ℝ)*X 0 0+(1088708771/2500000000 : ℝ)*X 0 1+(4354834913/10000000000 : ℝ)*X 0 2+(1957812109/5000000000 : ℝ)*X 1 0+(1088708771/2500000000 : ℝ)*X 1 1+(4354834913/10000000000 : ℝ)*X 1 2+(1957812109/5000000000 : ℝ)*X 2 0+(1088708771/2500000000 : ℝ)*X 2 1+(4354834913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1829163621/10000000000 : ℝ)*X 0 0+(1268013937/2500000000 : ℝ)*X 0 1+(5444052967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230751983/10000000000 : ℝ)*X 1 0+(-1615863261/10000000000 : ℝ)*X 1 1+(5444052647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230751783/10000000000 : ℝ)*X 2 0+(2722026371/5000000000 : ℝ)*X 2 1+(-403965851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1140164111/2500000000 : ℝ)*X 0 0+(4031434273/10000000000 : ℝ)*X 0 1+(2015717133/5000000000 : ℝ)*X 0 2+(1140164111/2500000000 : ℝ)*X 1 0+(4031434273/10000000000 : ℝ)*X 1 1+(2015717133/5000000000 : ℝ)*X 1 2+(1140164111/2500000000 : ℝ)*X 2 0+(4031434273/10000000000 : ℝ)*X 2 1+(2015717133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-378649623/2500000000 : ℝ)*X 0 0+(693929343/1250000000 : ℝ)*X 0 1+(2597504279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1350571381/2500000000 : ℝ)*X 1 0+(-860937367/5000000000 : ℝ)*X 1 1+(5195008167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1350571339/2500000000 : ℝ)*X 2 0+(5195007911/10000000000 : ℝ)*X 2 1+(-1721875309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3857893389/10000000000 : ℝ)*X 0 0+(547850473/1250000000 : ℝ)*X 0 1+(4382804117/10000000000 : ℝ)*X 0 2+(3857893389/10000000000 : ℝ)*X 1 0+(547850473/1250000000 : ℝ)*X 1 1+(4382804117/10000000000 : ℝ)*X 1 2+(3857893389/10000000000 : ℝ)*X 2 0+(547850473/1250000000 : ℝ)*X 2 1+(4382804117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1625_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6497/10000 : ℝ) ≤ (-5872472826060245624938232844351/9039062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2636739/100000000000000 : ℝ)*(lower0) + (12777457/100000000000000 : ℝ)*(upper3) + (392983/100000000000000 : ℝ)*(lower4) + (16092963/100000000000000 : ℝ)*(lower5) + (855480963913887/50000000000000 : ℝ)*(major0) + (855480963913887/50000000000000 : ℝ)*(major1) + (855480963913887/50000000000000 : ℝ)*(major2) + (475810963/50000000000000 : ℝ)*(sp1) + (616886084777881/25000000000000 : ℝ)*(sp4) + (616886097533637/25000000000000 : ℝ)*(sp5) + (616885324052267/25000000000000 : ℝ)*(sp6) + (976034420604219/100000000000000 : ℝ)*(sp7) + (20052899/2000000000000 : ℝ)*(sp8) + (2022773703/50000000000000 : ℝ)*(sp14) + (976034420604219/100000000000000 : ℝ)*(f.failure) + (1233772670878237/50000000000000 : ℝ)*(f.sum) + (1599563168269/2892500000000000000000000000 : ℝ)*base66 + (304761725027566453/36156250000000000000000000000000 : ℝ)*base68 + (19361766073472703/36156250000000000000000000000000 : ℝ)*base70 + (158823526556566453/36156250000000000000000000000000 : ℝ)*base72 + (6443137678517/1446250000000000000000000000 : ℝ)*base74 + (50010052709160203/36156250000000000000000000000000 : ℝ)*base76 + (96751935605878953/36156250000000000000000000000000 : ℝ)*base78 + (260911533857878953/36156250000000000000000000000000 : ℝ)*base80 + (22036184598517/5785000000000000000000000000 : ℝ)*base81 + (17841693/5000000000000000000000 : ℝ)*base89 + (17841693/5000000000000000000000 : ℝ)*base91 + (17841693/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14589/25000 : ℝ) ≤ (10550132489483442567089696916387/18078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12067407/100000000000000 : ℝ)*(lower1) + (13104093/100000000000000 : ℝ)*(upper2) + (167868581/100000000000000 : ℝ)*(lower5) + (224732216575029/12500000000000 : ℝ)*(major0) + (224732216575029/12500000000000 : ℝ)*(major1) + (224732216575029/12500000000000 : ℝ)*(major2) + (2550650214844303/100000000000000 : ℝ)*(sp0) + (2550632877803297/100000000000000 : ℝ)*(sp1) + (510128462227953/20000000000000 : ℝ)*(sp2) + (1025599789428021/100000000000000 : ℝ)*(sp3) + (15347820081/100000000000000 : ℝ)*(sp6) + (1291301053/25000000000000 : ℝ)*(sp7) + (7444115543/100000000000000 : ℝ)*(sp8) + (24781156549/100000000000000 : ℝ)*(sp9) + (1025604954632233/100000000000000 : ℝ)*(f.failure) + (1275328829479923/50000000000000 : ℝ)*(f.sum) + (10759720348251/5785000000000000000000000000 : ℝ)*base65 + (6038234338308797/1129882812500000000000000000000 : ℝ)*base68 + (14583225784981123/18078125000000000000000000000000 : ℝ)*base69 + (14984455415324873/18078125000000000000000000000000 : ℝ)*base71 + (18285992360257/2892500000000000000000000000 : ℝ)*base74 + (55220510674170249/9039062500000000000000000000000 : ℝ)*base75 + (19733037949326499/9039062500000000000000000000000 : ℝ)*base77 + (7379940095423501/9039062500000000000000000000000 : ℝ)*base80 + (3184639985027/723125000000000000000000000 : ℝ)*base81 + (5038751/5000000000000000000000 : ℝ)*base89 + (5038751/5000000000000000000000 : ℝ)*base91 + (5038751/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (10091/12500 : ℝ) ≤ (56133035262184079273376374211/69531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4218117/25000000000000 : ℝ)*(upper0) + (12221959/25000000000000 : ℝ)*(upper1) + (65008687/100000000000000 : ℝ)*(upper2) + (189928712430729/10000000000000 : ℝ)*(major0) + (189928712430729/10000000000000 : ℝ)*(major1) + (189928712430729/10000000000000 : ℝ)*(major2) + (32521564623/100000000000000 : ℝ)*(sp1) + (2703800137/10000000000000 : ℝ)*(sp2) + (4367713817/50000000000000 : ℝ)*(sp3) + (1460978579/25000000000000 : ℝ)*(sp4) + (1344095937353277/50000000000000 : ℝ)*(sp8) + (1344082598528123/50000000000000 : ℝ)*(sp9) + (2688170680619499/100000000000000 : ℝ)*(sp10) + (541728787707079/50000000000000 : ℝ)*(sp11) + (16929161106903/1562500000000 : ℝ)*(f.failure) + (268819771862087/10000000000000 : ℝ)*(f.sum) + (4134080138707/578500000000000000000000000 : ℝ)*base65 + (37599420790160551/7231250000000000000000000000000 : ℝ)*base68 + (36766134797498051/7231250000000000000000000000000 : ℝ)*base70 + (25140277621529301/7231250000000000000000000000000 : ℝ)*base72 + (37803651789057/1157000000000000000000000000 : ℝ)*base73 + (28484889219373051/7231250000000000000000000000000 : ℝ)*base76 + (11361821907333199/7231250000000000000000000000000 : ℝ)*base77 + (114305448085339449/7231250000000000000000000000000 : ℝ)*base79 + (33658131647/144625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2259/78125000000000000000 : ℝ)*base90 + (2259/78125000000000000000 : ℝ)*base92 + (2259/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-87977/100000 : ℝ) ≤ (-15904052665630372198016825520501/18078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25881403/50000000000000 : ℝ)*(lower0) + (353113/100000000000000 : ℝ)*(lower1) + (33959929/20000000000000 : ℝ)*(lower4) + (1942098594945657/100000000000000 : ℝ)*(major0) + (1942098594945657/100000000000000 : ℝ)*(major1) + (1942098594945657/100000000000000 : ℝ)*(major2) + (903339323/50000000000000 : ℝ)*(sp0) + (7535885503/10000000000000 : ℝ)*(sp5) + (164981546531/100000000000000 : ℝ)*(sp6) + (30942444393/100000000000000 : ℝ)*(sp7) + (561126307205429/20000000000000 : ℝ)*(sp12) + (2805557983850761/100000000000000 : ℝ)*(sp13) + (140273418057963/5000000000000 : ℝ)*(sp14) + (1107857576899013/100000000000000 : ℝ)*(sp15) + (553944259671703/50000000000000 : ℝ)*(f.failure) + (21919010489889/781250000000 : ℝ)*(f.sum) + (1572744555159/1446250000000000000000000000 : ℝ)*base65 + (204892963371866083/72312500000000000000000000000000 : ℝ)*base68 + (304374449657508917/72312500000000000000000000000000 : ℝ)*base69 + (85818080102446417/72312500000000000000000000000000 : ℝ)*base71 + (32114290659521/5785000000000000000000000000 : ℝ)*base73 + (94799303304696417/72312500000000000000000000000000 : ℝ)*base75 + (74717645587633917/72312500000000000000000000000000 : ℝ)*base77 + (270908557078071417/72312500000000000000000000000000 : ℝ)*base79 + (2829651789527/2892500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7135841/2500000000000000000000 : ℝ)*base89 + (7135841/2500000000000000000000 : ℝ)*base91 + (7135841/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1625_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3263/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1053/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6497/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14589/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (87977/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1625_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1625_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6497/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14589/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (87977/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1625_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1625_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1625_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4815/1024 : ℝ) ≤ p) (hpb : p ≤ (4819/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87648647/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8217/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6497/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14589/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (87977/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1625_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

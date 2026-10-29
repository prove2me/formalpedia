-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:08.27131+00:00
-- url     : https://prove2.me/submissions/0e38b3e6-c098-4c9f-b95d-47bc5b3370f3

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
theorem support_rectangle_w1617_s3_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210840631/1250000000 : ℝ)*x 0 + (2728885723/5000000000 : ℝ)*x 1 + (2590531277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210840631/1250000000 : ℝ)^4787 ≤ (5196070521109/50000000000000 : ℝ)^3763 := by
    have hnat : (210840631 : ℕ)^4787*50000000000000^3763 ≤ 5196070521109^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210840631 1250000000 5196070521109 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728885723/5000000000 : ℝ)^4787 ≤ (46286153480821/100000000000000 : ℝ)^3763 := by
    have hnat : (2728885723 : ℕ)^4787*100000000000000^3763 ≤ 46286153480821^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728885723 5000000000 46286153480821 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590531277/5000000000 : ℝ)^4787 ≤ (10830426365263/25000000000000 : ℝ)^3763 := by
    have hnat : (2590531277 : ℕ)^4787*25000000000000^3763 ≤ 10830426365263^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590531277 5000000000 10830426365263 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210840631/1250000000 : ℝ), (2728885723/5000000000 : ℝ), (2590531277/5000000000 : ℝ)] ![(5196070521109/50000000000000 : ℝ), (46286153480821/100000000000000 : ℝ), (10830426365263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210840631/1250000000 : ℝ)|^4787 ≤ (5196070521109/50000000000000 : ℝ)^3763
        have hw : |(-210840631/1250000000 : ℝ)|=(210840631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728885723/5000000000 : ℝ)|^4787 ≤ (46286153480821/100000000000000 : ℝ)^3763
        have hw : |(2728885723/5000000000 : ℝ)|=(2728885723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590531277/5000000000 : ℝ)|^4787 ≤ (10830426365263/25000000000000 : ℝ)^3763
        have hw : |(2590531277/5000000000 : ℝ)|=(2590531277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676345483/5000000000 : ℝ)*x 0 + (-914689093/5000000000 : ℝ)*x 1 + (1036212511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676345483/5000000000 : ℝ)^4787 ≤ (4515546637437/10000000000000 : ℝ)^3763 := by
    have hnat : (2676345483 : ℕ)^4787*10000000000000^3763 ≤ 4515546637437^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676345483 5000000000 4515546637437 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914689093/5000000000 : ℝ)^4787 ≤ (72017675913/625000000000 : ℝ)^3763 := by
    have hnat : (914689093 : ℕ)^4787*625000000000^3763 ≤ 72017675913^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914689093 5000000000 72017675913 625000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036212511/2000000000 : ℝ)^4787 ≤ (43321705471689/100000000000000 : ℝ)^3763 := by
    have hnat : (1036212511 : ℕ)^4787*100000000000000^3763 ≤ 43321705471689^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036212511 2000000000 43321705471689 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676345483/5000000000 : ℝ), (-914689093/5000000000 : ℝ), (1036212511/2000000000 : ℝ)] ![(4515546637437/10000000000000 : ℝ), (72017675913/625000000000 : ℝ), (43321705471689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676345483/5000000000 : ℝ)|^4787 ≤ (4515546637437/10000000000000 : ℝ)^3763
        have hw : |(2676345483/5000000000 : ℝ)|=(2676345483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914689093/5000000000 : ℝ)|^4787 ≤ (72017675913/625000000000 : ℝ)^3763
        have hw : |(-914689093/5000000000 : ℝ)|=(914689093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036212511/2000000000 : ℝ)|^4787 ≤ (43321705471689/100000000000000 : ℝ)^3763
        have hw : |(1036212511/2000000000 : ℝ)|=(1036212511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070538193/2000000000 : ℝ)*x 0 + (1036212511/2000000000 : ℝ)*x 1 + (-914689093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070538193/2000000000 : ℝ)^4787 ≤ (22577733181819/50000000000000 : ℝ)^3763 := by
    have hnat : (1070538193 : ℕ)^4787*50000000000000^3763 ≤ 22577733181819^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070538193 2000000000 22577733181819 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036212511/2000000000 : ℝ)^4787 ≤ (43321705471689/100000000000000 : ℝ)^3763 := by
    have hnat : (1036212511 : ℕ)^4787*100000000000000^3763 ≤ 43321705471689^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036212511 2000000000 43321705471689 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914689093/5000000000 : ℝ)^4787 ≤ (72017675913/625000000000 : ℝ)^3763 := by
    have hnat : (914689093 : ℕ)^4787*625000000000^3763 ≤ 72017675913^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914689093 5000000000 72017675913 625000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070538193/2000000000 : ℝ), (1036212511/2000000000 : ℝ), (-914689093/5000000000 : ℝ)] ![(22577733181819/50000000000000 : ℝ), (43321705471689/100000000000000 : ℝ), (72017675913/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070538193/2000000000 : ℝ)|^4787 ≤ (22577733181819/50000000000000 : ℝ)^3763
        have hw : |(1070538193/2000000000 : ℝ)|=(1070538193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036212511/2000000000 : ℝ)|^4787 ≤ (43321705471689/100000000000000 : ℝ)^3763
        have hw : |(1036212511/2000000000 : ℝ)|=(1036212511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-914689093/5000000000 : ℝ)|^4787 ≤ (72017675913/625000000000 : ℝ)^3763
        have hw : |(-914689093/5000000000 : ℝ)|=(914689093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206750201/10000000000 : ℝ)*x 0 + (1937145549/5000000000 : ℝ)*x 1 + (1140132717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206750201/10000000000 : ℝ)^4787 ≤ (1038637228517/3125000000000 : ℝ)^3763 := by
    have hnat : (4206750201 : ℕ)^4787*3125000000000^3763 ≤ 1038637228517^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206750201 10000000000 1038637228517 3125000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937145549/5000000000 : ℝ)^4787 ≤ (5986317646223/20000000000000 : ℝ)^3763 := by
    have hnat : (1937145549 : ℕ)^4787*20000000000000^3763 ≤ 5986317646223^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937145549 5000000000 5986317646223 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140132717/2500000000 : ℝ)^4787 ≤ (9208005108397/25000000000000 : ℝ)^3763 := by
    have hnat : (1140132717 : ℕ)^4787*25000000000000^3763 ≤ 9208005108397^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140132717 2500000000 9208005108397 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206750201/10000000000 : ℝ), (1937145549/5000000000 : ℝ), (1140132717/2500000000 : ℝ)] ![(1038637228517/3125000000000 : ℝ), (5986317646223/20000000000000 : ℝ), (9208005108397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206750201/10000000000 : ℝ)|^4787 ≤ (1038637228517/3125000000000 : ℝ)^3763
        have hw : |(4206750201/10000000000 : ℝ)|=(4206750201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1937145549/5000000000 : ℝ)|^4787 ≤ (5986317646223/20000000000000 : ℝ)^3763
        have hw : |(1937145549/5000000000 : ℝ)|=(1937145549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140132717/2500000000 : ℝ)|^4787 ≤ (9208005108397/25000000000000 : ℝ)^3763
        have hw : |(1140132717/2500000000 : ℝ)|=(1140132717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210849353/1250000000 : ℝ)*x 0 + (647891461/1250000000 : ℝ)*x 1 + (5455680491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210849353/1250000000 : ℝ)^4787 ≤ (5196343965151/50000000000000 : ℝ)^3763 := by
    have hnat : (210849353 : ℕ)^4787*50000000000000^3763 ≤ 5196343965151^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210849353 1250000000 5196343965151 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647891461/1250000000 : ℝ)^4787 ≤ (4334371587101/10000000000000 : ℝ)^3763 := by
    have hnat : (647891461 : ℕ)^4787*10000000000000^3763 ≤ 4334371587101^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647891461 1250000000 4334371587101 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455680491/10000000000 : ℝ)^4787 ≤ (23131798093397/50000000000000 : ℝ)^3763 := by
    have hnat : (5455680491 : ℕ)^4787*50000000000000^3763 ≤ 23131798093397^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455680491 10000000000 23131798093397 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210849353/1250000000 : ℝ), (647891461/1250000000 : ℝ), (5455680491/10000000000 : ℝ)] ![(5196343965151/50000000000000 : ℝ), (4334371587101/10000000000000 : ℝ), (23131798093397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210849353/1250000000 : ℝ)|^4787 ≤ (5196343965151/50000000000000 : ℝ)^3763
        have hw : |(-210849353/1250000000 : ℝ)|=(210849353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647891461/1250000000 : ℝ)|^4787 ≤ (4334371587101/10000000000000 : ℝ)^3763
        have hw : |(647891461/1250000000 : ℝ)|=(647891461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455680491/10000000000 : ℝ)|^4787 ≤ (23131798093397/50000000000000 : ℝ)^3763
        have hw : |(5455680491/10000000000 : ℝ)|=(5455680491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329944599/625000000 : ℝ)*x 0 + (-777380121/5000000000 : ℝ)*x 1 + (681960061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329944599/625000000 : ℝ)^4787 ≤ (44367339827543/100000000000000 : ℝ)^3763 := by
    have hnat : (329944599 : ℕ)^4787*100000000000000^3763 ≤ 44367339827543^3763*625000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329944599 625000000 44367339827543 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777380121/5000000000 : ℝ)^4787 ≤ (1873812800563/20000000000000 : ℝ)^3763 := by
    have hnat : (777380121 : ℕ)^4787*20000000000000^3763 ≤ 1873812800563^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777380121 5000000000 1873812800563 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681960061/1250000000 : ℝ)^4787 ≤ (722868689913/1562500000000 : ℝ)^3763 := by
    have hnat : (681960061 : ℕ)^4787*1562500000000^3763 ≤ 722868689913^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681960061 1250000000 722868689913 1562500000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329944599/625000000 : ℝ), (-777380121/5000000000 : ℝ), (681960061/1250000000 : ℝ)] ![(44367339827543/100000000000000 : ℝ), (1873812800563/20000000000000 : ℝ), (722868689913/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329944599/625000000 : ℝ)|^4787 ≤ (44367339827543/100000000000000 : ℝ)^3763
        have hw : |(329944599/625000000 : ℝ)|=(329944599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-777380121/5000000000 : ℝ)|^4787 ≤ (1873812800563/20000000000000 : ℝ)^3763
        have hw : |(-777380121/5000000000 : ℝ)|=(777380121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681960061/1250000000 : ℝ)|^4787 ≤ (722868689913/1562500000000 : ℝ)^3763
        have hw : |(681960061/1250000000 : ℝ)|=(681960061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639556789/5000000000 : ℝ)*x 0 + (340980031/625000000 : ℝ)*x 1 + (-1554760239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639556789/5000000000 : ℝ)^4787 ≤ (8873467952679/20000000000000 : ℝ)^3763 := by
    have hnat : (2639556789 : ℕ)^4787*20000000000000^3763 ≤ 8873467952679^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639556789 5000000000 8873467952679 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340980031/625000000 : ℝ)^4787 ≤ (46263596240731/100000000000000 : ℝ)^3763 := by
    have hnat : (340980031 : ℕ)^4787*100000000000000^3763 ≤ 46263596240731^3763*625000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340980031 625000000 46263596240731 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1554760239/10000000000 : ℝ)^4787 ≤ (9369063979817/100000000000000 : ℝ)^3763 := by
    have hnat : (1554760239 : ℕ)^4787*100000000000000^3763 ≤ 9369063979817^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554760239 10000000000 9369063979817 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639556789/5000000000 : ℝ), (340980031/625000000 : ℝ), (-1554760239/10000000000 : ℝ)] ![(8873467952679/20000000000000 : ℝ), (46263596240731/100000000000000 : ℝ), (9369063979817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639556789/5000000000 : ℝ)|^4787 ≤ (8873467952679/20000000000000 : ℝ)^3763
        have hw : |(2639556789/5000000000 : ℝ)|=(2639556789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340980031/625000000 : ℝ)|^4787 ≤ (46263596240731/100000000000000 : ℝ)^3763
        have hw : |(340980031/625000000 : ℝ)|=(340980031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1554760239/10000000000 : ℝ)|^4787 ≤ (9369063979817/100000000000000 : ℝ)^3763
        have hw : |(-1554760239/10000000000 : ℝ)|=(1554760239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s3_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051730809/2500000000 : ℝ)*x 0 + (2277699713/5000000000 : ℝ)*x 1 + (484934583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051730809/2500000000 : ℝ)^4787 ≤ (16619065222653/50000000000000 : ℝ)^3763 := by
    have hnat : (1051730809 : ℕ)^4787*50000000000000^3763 ≤ 16619065222653^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051730809 2500000000 16619065222653 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277699713/5000000000 : ℝ)^4787 ≤ (4597413512157/12500000000000 : ℝ)^3763 := by
    have hnat : (2277699713 : ℕ)^4787*12500000000000^3763 ≤ 4597413512157^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277699713 5000000000 4597413512157 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484934583/1250000000 : ℝ)^4787 ≤ (29982561436703/100000000000000 : ℝ)^3763 := by
    have hnat : (484934583 : ℕ)^4787*100000000000000^3763 ≤ 29982561436703^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484934583 1250000000 29982561436703 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051730809/2500000000 : ℝ), (2277699713/5000000000 : ℝ), (484934583/1250000000 : ℝ)] ![(16619065222653/50000000000000 : ℝ), (4597413512157/12500000000000 : ℝ), (29982561436703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051730809/2500000000 : ℝ)|^4787 ≤ (16619065222653/50000000000000 : ℝ)^3763
        have hw : |(1051730809/2500000000 : ℝ)|=(1051730809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2277699713/5000000000 : ℝ)|^4787 ≤ (4597413512157/12500000000000 : ℝ)^3763
        have hw : |(2277699713/5000000000 : ℝ)|=(2277699713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(484934583/1250000000 : ℝ)|^4787 ≤ (29982561436703/100000000000000 : ℝ)^3763
        have hw : |(484934583/1250000000 : ℝ)|=(484934583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (817/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3293/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3293/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3293/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3293/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3293/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3293/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10359/100000 : ℝ) ^ (4783/1024 : ℝ) ≤ (157227903093859/6250000000000000000 : ℝ) := by
    have hpowers : (10359/100000 : ℝ)^4783 ≤ (157227903093859/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10359 : ℕ)^4783*6250000000000000000^1024 ≤ 157227903093859^1024*100000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10359 100000 157227903093859 6250000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10359/100000 : ℝ)) (X := (157227903093859/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3293/20000 : ℝ) ^ (4783/1024 : ℝ) ≤ (10954925708035859/50000000000000000000 : ℝ) := by
    have hpowers : (3293/20000 : ℝ)^4783 ≤ (10954925708035859/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3293 : ℕ)^4783*50000000000000000000^1024 ≤ 10954925708035859^1024*20000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3293 20000 10954925708035859 50000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3293/20000 : ℝ)) (X := (10954925708035859/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125157227903093859/3125000000000000000 : ℝ) ≤ (2000021542722443/2000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (3125157227903093859/3125000000000000000 : ℝ)^1024 ≤ (2000021542722443/2000000000000000 : ℝ)^4783 := by
      have hnat : (3125157227903093859 : ℕ)^1024*2000000000000000^4783 ≤ 2000021542722443^4783*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125157227903093859 3125000000000000000 2000021542722443 2000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000021542722443/2000000000000000 : ℝ)) (X := (3125157227903093859/3125000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012212748932786731/50000000000000000000 : ℝ) ≤ (10000522879145179/10000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (50012212748932786731/50000000000000000000 : ℝ)^1024 ≤ (10000522879145179/10000000000000000 : ℝ)^4783 := by
      have hnat : (50012212748932786731 : ℕ)^1024*10000000000000000^4783 ≤ 10000522879145179^4783*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012212748932786731 50000000000000000000 10000522879145179 10000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000522879145179/10000000000000000 : ℝ)) (X := (50012212748932786731/50000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010954925708035859/25000000000000000000 : ℝ) ≤ (10000938044678143/10000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (25010954925708035859/25000000000000000000 : ℝ)^1024 ≤ (10000938044678143/10000000000000000 : ℝ)^4783 := by
      have hnat : (25010954925708035859 : ℕ)^1024*10000000000000000^4783 ≤ 10000938044678143^4783*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010954925708035859 25000000000000000000 10000938044678143 10000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000938044678143/10000000000000000 : ℝ)) (X := (25010954925708035859/25000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(157227903093859/6250000000000000000 : ℝ) ≤ ((30526028149902118319/30530000000000000000 : ℝ)+2*(103791383241/152650000000000 : ℝ)*(10359/100000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (30526028149902118319/30530000000000000000 : ℝ)+2*(103791383241/152650000000000 : ℝ)*(10359/100000 : ℝ)=(2000021542722443/2000000000000000 : ℝ) by norm_num, show 1+2*(157227903093859/6250000000000000000 : ℝ)=(3125157227903093859/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10954925708035859/50000000000000000000 : ℝ)+(157227903093859/6250000000000000000 : ℝ) ≤ ((30526028149902118319/30530000000000000000 : ℝ)+(103791383241/152650000000000 : ℝ)*((3293/20000 : ℝ)+(10359/100000 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (30526028149902118319/30530000000000000000 : ℝ)+(103791383241/152650000000000 : ℝ)*((3293/20000 : ℝ)+(10359/100000 : ℝ))=(10000522879145179/10000000000000000 : ℝ) by norm_num, show 1+(10954925708035859/50000000000000000000 : ℝ)+(157227903093859/6250000000000000000 : ℝ)=(50012212748932786731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10954925708035859/50000000000000000000 : ℝ) ≤ ((30526028149902118319/30530000000000000000 : ℝ)+2*(103791383241/152650000000000 : ℝ)*(3293/20000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (30526028149902118319/30530000000000000000 : ℝ)+2*(103791383241/152650000000000 : ℝ)*(3293/20000 : ℝ)=(10000938044678143/10000000000000000 : ℝ) by norm_num, show 1+2*(10954925708035859/50000000000000000000 : ℝ)=(25010954925708035859/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30526028149902118319/30530000000000000000 : ℝ)*(X 1 0+X 2 0)+(103791383241/152650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10359/100000 : ℝ)) (hi := (3293/20000 : ℝ)) (c := (30526028149902118319/30530000000000000000 : ℝ)) (alpha := (103791383241/152650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30526028149902118319/30530000000000000000 : ℝ)*(X 0 1+X 2 1)+(103791383241/152650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10359/100000 : ℝ)) (hi := (3293/20000 : ℝ)) (c := (30526028149902118319/30530000000000000000 : ℝ)) (alpha := (103791383241/152650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30526028149902118319/30530000000000000000 : ℝ)*(X 0 2+X 1 2)+(103791383241/152650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10359/100000 : ℝ)) (hi := (3293/20000 : ℝ)) (c := (30526028149902118319/30530000000000000000 : ℝ)) (alpha := (103791383241/152650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-210840631/1250000000 : ℝ)*X 0 0+(2728885723/5000000000 : ℝ)*X 0 1+(2590531277/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676345483/5000000000 : ℝ)*X 1 0+(-914689093/5000000000 : ℝ)*X 1 1+(1036212511/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070538193/2000000000 : ℝ)*X 2 0+(1036212511/2000000000 : ℝ)*X 2 1+(-914689093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206750201/10000000000 : ℝ)*X 0 0+(1937145549/5000000000 : ℝ)*X 0 1+(1140132717/2500000000 : ℝ)*X 0 2+(4206750201/10000000000 : ℝ)*X 1 0+(1937145549/5000000000 : ℝ)*X 1 1+(1140132717/2500000000 : ℝ)*X 1 2+(4206750201/10000000000 : ℝ)*X 2 0+(1937145549/5000000000 : ℝ)*X 2 1+(1140132717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210849353/1250000000 : ℝ)*X 0 0+(647891461/1250000000 : ℝ)*X 0 1+(5455680491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((329944599/625000000 : ℝ)*X 1 0+(-777380121/5000000000 : ℝ)*X 1 1+(681960061/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639556789/5000000000 : ℝ)*X 2 0+(340980031/625000000 : ℝ)*X 2 1+(-1554760239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1051730809/2500000000 : ℝ)*X 0 0+(2277699713/5000000000 : ℝ)*X 0 1+(484934583/1250000000 : ℝ)*X 0 2+(1051730809/2500000000 : ℝ)*X 1 0+(2277699713/5000000000 : ℝ)*X 1 1+(484934583/1250000000 : ℝ)*X 1 2+(1051730809/2500000000 : ℝ)*X 2 0+(2277699713/5000000000 : ℝ)*X 2 1+(484934583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (318302674082577720659165781/76325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (685615319/100000000000000 : ℝ)*(base19) + (320230931/50000000000000 : ℝ)*(base23) + (23807859/100000000000000 : ℝ)*(lower2) + (2078197/2000000000000 : ℝ)*(upper3) + (70925847/100000000000000 : ℝ)*(upper5) + (126778666768211/5000000000000 : ℝ)*(major0) + (126778666768211/5000000000000 : ℝ)*(major1) + (126778666768211/5000000000000 : ℝ)*(major2) + (1806957406358363/50000000000000 : ℝ)*(sp0) + (451740298437103/12500000000000 : ℝ)*(sp1) + (1806961216325141/50000000000000 : ℝ)*(sp2) + (1457219833259763/100000000000000 : ℝ)*(sp3) + (8260395417/100000000000000 : ℝ)*(sp4) + (3625344547/100000000000000 : ℝ)*(sp7) + (145722345860431/10000000000000 : ℝ)*(f.failure) + (3613923073112143/100000000000000 : ℝ)*(f.sum) + (7502878571861/3053000000000000000000000000 : ℝ)*base65 + (1182923397803042691/152650000000000000000000000000000 : ℝ)*base68 + (1022885741533792691/152650000000000000000000000000000 : ℝ)*base70 + (2274439430173192691/152650000000000000000000000000000 : ℝ)*base72 + (1803473044153/763250000000000000000000000 : ℝ)*base73 + (2312325995911642691/152650000000000000000000000000000 : ℝ)*base76 + (1402443118960092691/152650000000000000000000000000000 : ℝ)*base78 + (2612996044170742691/152650000000000000000000000000000 : ℝ)*base80 + (1812359217711/381625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1073361/100000000000000000000 : ℝ)*base89 + (1073361/100000000000000000000 : ℝ)*base91 + (1073361/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13159828477522525000057540029/1526500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (662754619/50000000000000 : ℝ)*(base19) + (1428396521/100000000000000 : ℝ)*(base23) + (91793753/50000000000000 : ℝ)*(upper3) + (23683273/50000000000000 : ℝ)*(lower4) + (43974569/25000000000000 : ℝ)*(upper5) + (2574262970355697/100000000000000 : ℝ)*(major0) + (2574262970355697/100000000000000 : ℝ)*(major1) + (2574262970355697/100000000000000 : ℝ)*(major2) + (15208967547/100000000000000 : ℝ)*(sp1) + (8226295187/50000000000000 : ℝ)*(sp2) + (1834533405974537/50000000000000 : ℝ)*(sp4) + (366905027747229/10000000000000 : ℝ)*(sp5) + (3669048930962179/100000000000000 : ℝ)*(sp6) + (739729420699221/50000000000000 : ℝ)*(sp7) + (739729420699221/50000000000000 : ℝ)*(f.failure) + (1834533405974537/50000000000000 : ℝ)*(f.sum) + (10563345053043/7632500000000000000000000000 : ℝ)*base66 + (18537527590193113343/3053000000000000000000000000000000 : ℝ)*base67 + (22839542109560886657/3053000000000000000000000000000000 : ℝ)*base70 + (9348314507916886657/3053000000000000000000000000000000 : ℝ)*base72 + (2588886321869/954062500000000000000000000 : ℝ)*base73 + (46586584455423886657/3053000000000000000000000000000000 : ℝ)*base76 + (19064394227246886657/3053000000000000000000000000000000 : ℝ)*base78 + (26239790343767113343/3053000000000000000000000000000000 : ℝ)*base79 + (59969548209941/15265000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2075851/500000000000000000000 : ℝ)*base89 + (2075851/500000000000000000000 : ℝ)*base91 + (2075851/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1617_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (817/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1617_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1617_s4_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686824099/10000000000 : ℝ)*x 0 + (5457275797/10000000000 : ℝ)*x 1 + (207259691/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686824099/10000000000 : ℝ)^4787 ≤ (10392917382787/100000000000000 : ℝ)^3763 := by
    have hnat : (1686824099 : ℕ)^4787*100000000000000^3763 ≤ 10392917382787^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686824099 10000000000 10392917382787 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457275797/10000000000 : ℝ)^4787 ≤ (46280806189771/100000000000000 : ℝ)^3763 := by
    have hnat : (5457275797 : ℕ)^4787*100000000000000^3763 ≤ 46280806189771^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457275797 10000000000 46280806189771 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207259691/400000000 : ℝ)^4787 ≤ (10831569105201/25000000000000 : ℝ)^3763 := by
    have hnat : (207259691 : ℕ)^4787*25000000000000^3763 ≤ 10831569105201^3763*400000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207259691 400000000 10831569105201 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686824099/10000000000 : ℝ), (5457275797/10000000000 : ℝ), (207259691/400000000 : ℝ)] ![(10392917382787/100000000000000 : ℝ), (46280806189771/100000000000000 : ℝ), (10831569105201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686824099/10000000000 : ℝ)|^4787 ≤ (10392917382787/100000000000000 : ℝ)^3763
        have hw : |(-1686824099/10000000000 : ℝ)|=(1686824099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457275797/10000000000 : ℝ)|^4787 ≤ (46280806189771/100000000000000 : ℝ)^3763
        have hw : |(5457275797/10000000000 : ℝ)|=(5457275797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207259691/400000000 : ℝ)|^4787 ≤ (10831569105201/25000000000000 : ℝ)^3763
        have hw : |(207259691/400000000 : ℝ)|=(207259691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352557393/10000000000 : ℝ)*x 0 + (-57155807/312500000 : ℝ)*x 1 + (518149287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352557393/10000000000 : ℝ)^4787 ≤ (22577016458839/50000000000000 : ℝ)^3763 := by
    have hnat : (5352557393 : ℕ)^4787*50000000000000^3763 ≤ 22577016458839^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352557393 10000000000 22577016458839 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57155807/312500000 : ℝ)^4787 ≤ (2303936863203/20000000000000 : ℝ)^3763 := by
    have hnat : (57155807 : ℕ)^4787*20000000000000^3763 ≤ 2303936863203^3763*312500000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57155807 312500000 2303936863203 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518149287/1000000000 : ℝ)^4787 ≤ (8665256549983/20000000000000 : ℝ)^3763 := by
    have hnat : (518149287 : ℕ)^4787*20000000000000^3763 ≤ 8665256549983^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518149287 1000000000 8665256549983 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352557393/10000000000 : ℝ), (-57155807/312500000 : ℝ), (518149287/1000000000 : ℝ)] ![(22577016458839/50000000000000 : ℝ), (2303936863203/20000000000000 : ℝ), (8665256549983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352557393/10000000000 : ℝ)|^4787 ≤ (22577016458839/50000000000000 : ℝ)^3763
        have hw : |(5352557393/10000000000 : ℝ)|=(5352557393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57155807/312500000 : ℝ)|^4787 ≤ (2303936863203/20000000000000 : ℝ)^3763
        have hw : |(-57155807/312500000 : ℝ)|=(57155807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518149287/1000000000 : ℝ)|^4787 ≤ (8665256549983/20000000000000 : ℝ)^3763
        have hw : |(518149287/1000000000 : ℝ)|=(518149287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338139487/2500000000 : ℝ)*x 0 + (2590746021/5000000000 : ℝ)*x 1 + (-1828986181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338139487/2500000000 : ℝ)^4787 ≤ (9030807774743/20000000000000 : ℝ)^3763 := by
    have hnat : (1338139487 : ℕ)^4787*20000000000000^3763 ≤ 9030807774743^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338139487 2500000000 9030807774743 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590746021/5000000000 : ℝ)^4787 ≤ (21663136971173/50000000000000 : ℝ)^3763 := by
    have hnat : (2590746021 : ℕ)^4787*50000000000000^3763 ≤ 21663136971173^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590746021 5000000000 21663136971173 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1828986181/10000000000 : ℝ)^4787 ≤ (11519687176421/100000000000000 : ℝ)^3763 := by
    have hnat : (1828986181 : ℕ)^4787*100000000000000^3763 ≤ 11519687176421^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828986181 10000000000 11519687176421 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338139487/2500000000 : ℝ), (2590746021/5000000000 : ℝ), (-1828986181/10000000000 : ℝ)] ![(9030807774743/20000000000000 : ℝ), (21663136971173/50000000000000 : ℝ), (11519687176421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338139487/2500000000 : ℝ)|^4787 ≤ (9030807774743/20000000000000 : ℝ)^3763
        have hw : |(1338139487/2500000000 : ℝ)|=(1338139487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590746021/5000000000 : ℝ)|^4787 ≤ (21663136971173/50000000000000 : ℝ)^3763
        have hw : |(2590746021/5000000000 : ℝ)|=(2590746021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1828986181/10000000000 : ℝ)|^4787 ≤ (11519687176421/100000000000000 : ℝ)^3763
        have hw : |(-1828986181/10000000000 : ℝ)|=(1828986181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2103407233/5000000000 : ℝ)*x 0 + (1937715493/5000000000 : ℝ)*x 1 + (1139844377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103407233/5000000000 : ℝ)^4787 ≤ (33237037222179/100000000000000 : ℝ)^3763 := by
    have hnat : (2103407233 : ℕ)^4787*100000000000000^3763 ≤ 33237037222179^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103407233 5000000000 33237037222179 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937715493/5000000000 : ℝ)^4787 ≤ (14971395769719/50000000000000 : ℝ)^3763 := by
    have hnat : (1937715493 : ℕ)^4787*50000000000000^3763 ≤ 14971395769719^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937715493 5000000000 14971395769719 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139844377/2500000000 : ℝ)^4787 ≤ (36820171226419/100000000000000 : ℝ)^3763 := by
    have hnat : (1139844377 : ℕ)^4787*100000000000000^3763 ≤ 36820171226419^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139844377 2500000000 36820171226419 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103407233/5000000000 : ℝ), (1937715493/5000000000 : ℝ), (1139844377/2500000000 : ℝ)] ![(33237037222179/100000000000000 : ℝ), (14971395769719/50000000000000 : ℝ), (36820171226419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103407233/5000000000 : ℝ)|^4787 ≤ (33237037222179/100000000000000 : ℝ)^3763
        have hw : |(2103407233/5000000000 : ℝ)|=(2103407233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1937715493/5000000000 : ℝ)|^4787 ≤ (14971395769719/50000000000000 : ℝ)^3763
        have hw : |(1937715493/5000000000 : ℝ)|=(1937715493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139844377/2500000000 : ℝ)|^4787 ≤ (36820171226419/100000000000000 : ℝ)^3763
        have hw : |(1139844377/2500000000 : ℝ)|=(1139844377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686893247/10000000000 : ℝ)*x 0 + (5183547503/10000000000 : ℝ)*x 1 + (5455198913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686893247/10000000000 : ℝ)^4787 ≤ (5196729678693/50000000000000 : ℝ)^3763 := by
    have hnat : (1686893247 : ℕ)^4787*50000000000000^3763 ≤ 5196729678693^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686893247 10000000000 5196729678693 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183547503/10000000000 : ℝ)^4787 ≤ (866962787821/2000000000000 : ℝ)^3763 := by
    have hnat : (5183547503 : ℕ)^4787*2000000000000^3763 ≤ 866962787821^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183547503 10000000000 866962787821 2000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455198913/10000000000 : ℝ)^4787 ≤ (46258401240141/100000000000000 : ℝ)^3763 := by
    have hnat : (5455198913 : ℕ)^4787*100000000000000^3763 ≤ 46258401240141^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455198913 10000000000 46258401240141 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686893247/10000000000 : ℝ), (5183547503/10000000000 : ℝ), (5455198913/10000000000 : ℝ)] ![(5196729678693/50000000000000 : ℝ), (866962787821/2000000000000 : ℝ), (46258401240141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686893247/10000000000 : ℝ)|^4787 ≤ (5196729678693/50000000000000 : ℝ)^3763
        have hw : |(-1686893247/10000000000 : ℝ)|=(1686893247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183547503/10000000000 : ℝ)|^4787 ≤ (866962787821/2000000000000 : ℝ)^3763
        have hw : |(5183547503/10000000000 : ℝ)|=(5183547503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455198913/10000000000 : ℝ)|^4787 ≤ (46258401240141/100000000000000 : ℝ)^3763
        have hw : |(5455198913/10000000000 : ℝ)|=(5455198913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279227351/10000000000 : ℝ)*x 0 + (-1555279171/10000000000 : ℝ)*x 1 + (2727599473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279227351/10000000000 : ℝ)^4787 ≤ (11092139037813/25000000000000 : ℝ)^3763 := by
    have hnat : (5279227351 : ℕ)^4787*25000000000000^3763 ≤ 11092139037813^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279227351 10000000000 11092139037813 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1555279171/10000000000 : ℝ)^4787 ≤ (117163027883/1250000000000 : ℝ)^3763 := by
    have hnat : (1555279171 : ℕ)^4787*1250000000000^3763 ≤ 117163027883^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555279171 10000000000 117163027883 1250000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727599473/5000000000 : ℝ)^4787 ≤ (46258401596119/100000000000000 : ℝ)^3763 := by
    have hnat : (2727599473 : ℕ)^4787*100000000000000^3763 ≤ 46258401596119^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727599473 5000000000 46258401596119 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279227351/10000000000 : ℝ), (-1555279171/10000000000 : ℝ), (2727599473/5000000000 : ℝ)] ![(11092139037813/25000000000000 : ℝ), (117163027883/1250000000000 : ℝ), (46258401596119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279227351/10000000000 : ℝ)|^4787 ≤ (11092139037813/25000000000000 : ℝ)^3763
        have hw : |(5279227351/10000000000 : ℝ)|=(5279227351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1555279171/10000000000 : ℝ)|^4787 ≤ (117163027883/1250000000000 : ℝ)^3763
        have hw : |(-1555279171/10000000000 : ℝ)|=(1555279171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727599473/5000000000 : ℝ)|^4787 ≤ (46258401596119/100000000000000 : ℝ)^3763
        have hw : |(2727599473/5000000000 : ℝ)|=(2727599473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319806837/2500000000 : ℝ)*x 0 + (5455198909/10000000000 : ℝ)*x 1 + (-388819807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319806837/2500000000 : ℝ)^4787 ≤ (22184278059589/50000000000000 : ℝ)^3763 := by
    have hnat : (1319806837 : ℕ)^4787*50000000000000^3763 ≤ 22184278059589^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319806837 2500000000 22184278059589 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455198909/10000000000 : ℝ)^4787 ≤ (722787518703/1562500000000 : ℝ)^3763 := by
    have hnat : (5455198909 : ℕ)^4787*1562500000000^3763 ≤ 722787518703^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455198909 10000000000 722787518703 1562500000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388819807/2500000000 : ℝ)^4787 ≤ (1874608533527/20000000000000 : ℝ)^3763 := by
    have hnat : (388819807 : ℕ)^4787*20000000000000^3763 ≤ 1874608533527^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388819807 2500000000 1874608533527 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319806837/2500000000 : ℝ), (5455198909/10000000000 : ℝ), (-388819807/2500000000 : ℝ)] ![(22184278059589/50000000000000 : ℝ), (722787518703/1562500000000 : ℝ), (1874608533527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319806837/2500000000 : ℝ)|^4787 ≤ (22184278059589/50000000000000 : ℝ)^3763
        have hw : |(1319806837/2500000000 : ℝ)|=(1319806837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455198909/10000000000 : ℝ)|^4787 ≤ (722787518703/1562500000000 : ℝ)^3763
        have hw : |(5455198909/10000000000 : ℝ)|=(5455198909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-388819807/2500000000 : ℝ)|^4787 ≤ (1874608533527/20000000000000 : ℝ)^3763
        have hw : |(-388819807/2500000000 : ℝ)|=(388819807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s4_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206985779/10000000000 : ℝ)*x 0 + (4554279641/10000000000 : ℝ)*x 1 + (3880582457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206985779/10000000000 : ℝ)^4787 ≤ (33238759054599/100000000000000 : ℝ)^3763 := by
    have hnat : (4206985779 : ℕ)^4787*100000000000000^3763 ≤ 33238759054599^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206985779 10000000000 33238759054599 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4554279641/10000000000 : ℝ)^4787 ≤ (18383903670219/50000000000000 : ℝ)^3763 := by
    have hnat : (4554279641 : ℕ)^4787*50000000000000^3763 ≤ 18383903670219^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554279641 10000000000 18383903670219 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3880582457/10000000000 : ℝ)^4787 ≤ (29993433587703/100000000000000 : ℝ)^3763 := by
    have hnat : (3880582457 : ℕ)^4787*100000000000000^3763 ≤ 29993433587703^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880582457 10000000000 29993433587703 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206985779/10000000000 : ℝ), (4554279641/10000000000 : ℝ), (3880582457/10000000000 : ℝ)] ![(33238759054599/100000000000000 : ℝ), (18383903670219/50000000000000 : ℝ), (29993433587703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206985779/10000000000 : ℝ)|^4787 ≤ (33238759054599/100000000000000 : ℝ)^3763
        have hw : |(4206985779/10000000000 : ℝ)|=(4206985779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4554279641/10000000000 : ℝ)|^4787 ≤ (18383903670219/50000000000000 : ℝ)^3763
        have hw : |(4554279641/10000000000 : ℝ)|=(4554279641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3880582457/10000000000 : ℝ)|^4787 ≤ (29993433587703/100000000000000 : ℝ)^3763
        have hw : |(3880582457/10000000000 : ℝ)|=(3880582457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (131/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1633/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (817/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (817/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (817/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (817/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (817/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (817/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10471/100000 : ℝ) ^ (4783/1024 : ℝ) ≤ (20665896797537/781250000000000000 : ℝ) := by
    have hpowers : (10471/100000 : ℝ)^4783 ≤ (20665896797537/781250000000000000 : ℝ)^1024 := by
      have hnat : (10471 : ℕ)^4783*781250000000000000^1024 ≤ 20665896797537^1024*100000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10471 100000 20665896797537 781250000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10471/100000 : ℝ)) (X := (20665896797537/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (817/5000 : ℝ) ^ (4783/1024 : ℝ) ≤ (2642957946549297/12500000000000000000 : ℝ) := by
    have hpowers : (817/5000 : ℝ)^4783 ≤ (2642957946549297/12500000000000000000 : ℝ)^1024 := by
      have hnat : (817 : ℕ)^4783*12500000000000000000^1024 ≤ 2642957946549297^1024*5000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        817 5000 2642957946549297 12500000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (817/5000 : ℝ)) (X := (2642957946549297/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (390645665896797537/390625000000000000 : ℝ) ≤ (10000113262141539/10000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (390645665896797537/390625000000000000 : ℝ)^1024 ≤ (10000113262141539/10000000000000000 : ℝ)^4783 := by
      have hnat : (390645665896797537 : ℕ)^1024*10000000000000000^4783 ≤ 10000113262141539^4783*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390645665896797537 390625000000000000 10000113262141539 10000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000113262141539/10000000000000000 : ℝ)) (X := (390645665896797537/390625000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502973612295309889/12500000000000000000 : ℝ) ≤ (312515914145869/312500000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (12502973612295309889/12500000000000000000 : ℝ)^1024 ≤ (312515914145869/312500000000000 : ℝ)^4783 := by
      have hnat : (12502973612295309889 : ℕ)^1024*312500000000000^4783 ≤ 312515914145869^4783*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502973612295309889 12500000000000000000 312515914145869 312500000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312515914145869/312500000000000 : ℝ)) (X := (12502973612295309889/12500000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252642957946549297/6250000000000000000 : ℝ) ≤ (10000905243194077/10000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (6252642957946549297/6250000000000000000 : ℝ)^1024 ≤ (10000905243194077/10000000000000000 : ℝ)^4783 := by
      have hnat : (6252642957946549297 : ℕ)^1024*10000000000000000^4783 ≤ 10000905243194077^4783*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252642957946549297 6250000000000000000 10000905243194077 10000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000905243194077/10000000000000000 : ℝ)) (X := (6252642957946549297/6250000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20665896797537/781250000000000000 : ℝ) ≤ ((58682371901907566993/58690000000000000000 : ℝ)+2*(395990526269/586900000000000 : ℝ)*(10471/100000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (58682371901907566993/58690000000000000000 : ℝ)+2*(395990526269/586900000000000 : ℝ)*(10471/100000 : ℝ)=(10000113262141539/10000000000000000 : ℝ) by norm_num, show 1+2*(20665896797537/781250000000000000 : ℝ)=(390645665896797537/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2642957946549297/12500000000000000000 : ℝ)+(20665896797537/781250000000000000 : ℝ) ≤ ((58682371901907566993/58690000000000000000 : ℝ)+(395990526269/586900000000000 : ℝ)*((817/5000 : ℝ)+(10471/100000 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (58682371901907566993/58690000000000000000 : ℝ)+(395990526269/586900000000000 : ℝ)*((817/5000 : ℝ)+(10471/100000 : ℝ))=(312515914145869/312500000000000 : ℝ) by norm_num, show 1+(2642957946549297/12500000000000000000 : ℝ)+(20665896797537/781250000000000000 : ℝ)=(12502973612295309889/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2642957946549297/12500000000000000000 : ℝ) ≤ ((58682371901907566993/58690000000000000000 : ℝ)+2*(395990526269/586900000000000 : ℝ)*(817/5000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (58682371901907566993/58690000000000000000 : ℝ)+2*(395990526269/586900000000000 : ℝ)*(817/5000 : ℝ)=(10000905243194077/10000000000000000 : ℝ) by norm_num, show 1+2*(2642957946549297/12500000000000000000 : ℝ)=(6252642957946549297/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58682371901907566993/58690000000000000000 : ℝ)*(X 1 0+X 2 0)+(395990526269/586900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10471/100000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (58682371901907566993/58690000000000000000 : ℝ)) (alpha := (395990526269/586900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58682371901907566993/58690000000000000000 : ℝ)*(X 0 1+X 2 1)+(395990526269/586900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10471/100000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (58682371901907566993/58690000000000000000 : ℝ)) (alpha := (395990526269/586900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58682371901907566993/58690000000000000000 : ℝ)*(X 0 2+X 1 2)+(395990526269/586900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10471/100000 : ℝ)) (hi := (817/5000 : ℝ)) (c := (58682371901907566993/58690000000000000000 : ℝ)) (alpha := (395990526269/586900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1686824099/10000000000 : ℝ)*X 0 0+(5457275797/10000000000 : ℝ)*X 0 1+(207259691/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352557393/10000000000 : ℝ)*X 1 0+(-57155807/312500000 : ℝ)*X 1 1+(518149287/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338139487/2500000000 : ℝ)*X 2 0+(2590746021/5000000000 : ℝ)*X 2 1+(-1828986181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2103407233/5000000000 : ℝ)*X 0 0+(1937715493/5000000000 : ℝ)*X 0 1+(1139844377/2500000000 : ℝ)*X 0 2+(2103407233/5000000000 : ℝ)*X 1 0+(1937715493/5000000000 : ℝ)*X 1 1+(1139844377/2500000000 : ℝ)*X 1 2+(2103407233/5000000000 : ℝ)*X 2 0+(1937715493/5000000000 : ℝ)*X 2 1+(1139844377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1686893247/10000000000 : ℝ)*X 0 0+(5183547503/10000000000 : ℝ)*X 0 1+(5455198913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279227351/10000000000 : ℝ)*X 1 0+(-1555279171/10000000000 : ℝ)*X 1 1+(2727599473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319806837/2500000000 : ℝ)*X 2 0+(5455198909/10000000000 : ℝ)*X 2 1+(-388819807/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206985779/10000000000 : ℝ)*X 0 0+(4554279641/10000000000 : ℝ)*X 0 1+(3880582457/10000000000 : ℝ)*X 0 2+(4206985779/10000000000 : ℝ)*X 1 0+(4554279641/10000000000 : ℝ)*X 1 1+(3880582457/10000000000 : ℝ)*X 1 2+(4206985779/10000000000 : ℝ)*X 2 0+(4554279641/10000000000 : ℝ)*X 2 1+(3880582457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225629913747823016394819/29345000000000000000000000000 : ℝ) := by norm_num
    linear_combination (692876199/100000000000000 : ℝ)*(base19) + (242967087/25000000000000 : ℝ)*(base23) + (10998371/20000000000000 : ℝ)*(lower2) + (7135781/2500000000000 : ℝ)*(upper3) + (1538977/50000000000000 : ℝ)*(lower4) + (2544085992614151/100000000000000 : ℝ)*(major0) + (2544085992614151/100000000000000 : ℝ)*(major1) + (2544085992614151/100000000000000 : ℝ)*(major2) + (1813023147639771/50000000000000 : ℝ)*(sp0) + (453256906801933/12500000000000 : ℝ)*(sp1) + (906513743855829/25000000000000 : ℝ)*(sp2) + (365526906271017/25000000000000 : ℝ)*(sp3) + (9652012121/100000000000000 : ℝ)*(sp4) + (8156556867/100000000000000 : ℝ)*(sp7) + (182764472705117/12500000000000 : ℝ)*(f.failure) + (226628496705729/6250000000000 : ℝ)*(f.sum) + (139054155663699/29345000000000000000000000000 : ℝ)*base65 + (1123197374286217943/5869000000000000000000000000000000 : ℝ)*base67 + (35194017977960217943/5869000000000000000000000000000000 : ℝ)*base69 + (44210796575217217943/5869000000000000000000000000000000 : ℝ)*base71 + (8510038947283/3668125000000000000000000000 : ℝ)*base73 + (918990494472782057/5869000000000000000000000000000000 : ℝ)*base76 + (55524584402486782057/5869000000000000000000000000000000 : ℝ)*base78 + (50489507196728782057/5869000000000000000000000000000000 : ℝ)*base80 + (66131612333501/7336250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (908627/125000000000000000000 : ℝ)*base89 + (908627/125000000000000000000 : ℝ)*base91 + (908627/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7161741912348149930674656063/586900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1937797299/100000000000000 : ℝ)*(base19) + (2053623371/100000000000000 : ℝ)*(base23) + (321596079/50000000000000 : ℝ)*(lower1) + (124822997/50000000000000 : ℝ)*(upper3) + (57706887/100000000000000 : ℝ)*(lower4) + (30620543/12500000000000 : ℝ)*(upper5) + (516550071579003/20000000000000 : ℝ)*(major0) + (516550071579003/20000000000000 : ℝ)*(major1) + (516550071579003/20000000000000 : ℝ)*(major2) + (619752367/100000000000000 : ℝ)*(sp2) + (3681163667395881/100000000000000 : ℝ)*(sp4) + (1840580864799291/50000000000000 : ℝ)*(sp5) + (230072562126259/6250000000000 : ℝ)*(sp6) + (1187469313311/80000000000 : ℝ)*(sp7) + (1187469313311/80000000000 : ℝ)*(f.failure) + (3681163667395881/100000000000000 : ℝ)*(f.sum) + (652945849401/146725000000000000000000000 : ℝ)*base65 + (20055924920891947979/1173800000000000000000000000000000 : ℝ)*base67 + (618662938793947979/1173800000000000000000000000000000 : ℝ)*base69 + (43277646224433747979/1173800000000000000000000000000000 : ℝ)*base71 + (1407386433387/234760000000000000000000000 : ℝ)*base73 + (102625988152868252021/1173800000000000000000000000000000 : ℝ)*base76 + (903296321578947979/1173800000000000000000000000000000 : ℝ)*base77 + (16594748958932652021/1173800000000000000000000000000000 : ℝ)*base80 + (1979793635359/733625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7359/800000000000000000 : ℝ)*base90 + (7359/800000000000000000 : ℝ)*base92 + (7359/800000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1617_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (817/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1617_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1617_s5_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686831937/10000000000 : ℝ)*x 0 + (545723713/1000000000 : ℝ)*x 1 + (1036305143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686831937/10000000000 : ℝ)^4787 ≤ (5196489407943/50000000000000 : ℝ)^3763 := by
    have hnat : (1686831937 : ℕ)^4787*50000000000000^3763 ≤ 5196489407943^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686831937 10000000000 5196489407943 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545723713/1000000000 : ℝ)^4787 ≤ (46280389037817/100000000000000 : ℝ)^3763 := by
    have hnat : (545723713 : ℕ)^4787*100000000000000^3763 ≤ 46280389037817^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545723713 1000000000 46280389037817 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036305143/2000000000 : ℝ)^4787 ≤ (4332663212777/10000000000000 : ℝ)^3763 := by
    have hnat : (1036305143 : ℕ)^4787*10000000000000^3763 ≤ 4332663212777^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036305143 2000000000 4332663212777 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686831937/10000000000 : ℝ), (545723713/1000000000 : ℝ), (1036305143/2000000000 : ℝ)] ![(5196489407943/50000000000000 : ℝ), (46280389037817/100000000000000 : ℝ), (4332663212777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686831937/10000000000 : ℝ)|^4787 ≤ (5196489407943/50000000000000 : ℝ)^3763
        have hw : |(-1686831937/10000000000 : ℝ)|=(1686831937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545723713/1000000000 : ℝ)|^4787 ≤ (46280389037817/100000000000000 : ℝ)^3763
        have hw : |(545723713/1000000000 : ℝ)|=(545723713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036305143/2000000000 : ℝ)|^4787 ≤ (4332663212777/10000000000000 : ℝ)^3763
        have hw : |(1036305143/2000000000 : ℝ)|=(1036305143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338136901/2500000000 : ℝ)*x 0 + (-45723883/250000000 : ℝ)*x 1 + (5181525723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338136901/2500000000 : ℝ)^4787 ≤ (9030785573217/20000000000000 : ℝ)^3763 := by
    have hnat : (1338136901 : ℕ)^4787*20000000000000^3763 ≤ 9030785573217^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338136901 2500000000 9030785573217 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45723883/250000000 : ℝ)^4787 ≤ (5759719954053/50000000000000 : ℝ)^3763 := by
    have hnat : (45723883 : ℕ)^4787*50000000000000^3763 ≤ 5759719954053^3763*250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45723883 250000000 5759719954053 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181525723/10000000000 : ℝ)^4787 ≤ (10831658053217/25000000000000 : ℝ)^3763 := by
    have hnat : (5181525723 : ℕ)^4787*25000000000000^3763 ≤ 10831658053217^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181525723 10000000000 10831658053217 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338136901/2500000000 : ℝ), (-45723883/250000000 : ℝ), (5181525723/10000000000 : ℝ)] ![(9030785573217/20000000000000 : ℝ), (5759719954053/50000000000000 : ℝ), (10831658053217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338136901/2500000000 : ℝ)|^4787 ≤ (9030785573217/20000000000000 : ℝ)^3763
        have hw : |(1338136901/2500000000 : ℝ)|=(1338136901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45723883/250000000 : ℝ)|^4787 ≤ (5759719954053/50000000000000 : ℝ)^3763
        have hw : |(-45723883/250000000 : ℝ)|=(45723883/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181525723/10000000000 : ℝ)|^4787 ≤ (10831658053217/25000000000000 : ℝ)^3763
        have hw : |(5181525723/10000000000 : ℝ)|=(5181525723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352547439/10000000000 : ℝ)*x 0 + (5181525849/10000000000 : ℝ)*x 1 + (-1828955373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352547439/10000000000 : ℝ)^4787 ≤ (11288481523843/25000000000000 : ℝ)^3763 := by
    have hnat : (5352547439 : ℕ)^4787*25000000000000^3763 ≤ 11288481523843^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352547439 10000000000 11288481523843 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181525849/10000000000 : ℝ)^4787 ≤ (169244662317/390625000000 : ℝ)^3763 := by
    have hnat : (5181525849 : ℕ)^4787*390625000000^3763 ≤ 169244662317^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181525849 10000000000 169244662317 390625000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1828955373/10000000000 : ℝ)^4787 ≤ (11519440332759/100000000000000 : ℝ)^3763 := by
    have hnat : (1828955373 : ℕ)^4787*100000000000000^3763 ≤ 11519440332759^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828955373 10000000000 11519440332759 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352547439/10000000000 : ℝ), (5181525849/10000000000 : ℝ), (-1828955373/10000000000 : ℝ)] ![(11288481523843/25000000000000 : ℝ), (169244662317/390625000000 : ℝ), (11519440332759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352547439/10000000000 : ℝ)|^4787 ≤ (11288481523843/25000000000000 : ℝ)^3763
        have hw : |(5352547439/10000000000 : ℝ)|=(5352547439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181525849/10000000000 : ℝ)|^4787 ≤ (169244662317/390625000000 : ℝ)^3763
        have hw : |(5181525849/10000000000 : ℝ)|=(5181525849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1828955373/10000000000 : ℝ)|^4787 ≤ (11519440332759/100000000000000 : ℝ)^3763
        have hw : |(-1828955373/10000000000 : ℝ)|=(1828955373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206819779/10000000000 : ℝ)*x 0 + (1937760407/5000000000 : ℝ)*x 1 + (142477699/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206819779/10000000000 : ℝ)^4787 ≤ (4154636327723/12500000000000 : ℝ)^3763 := by
    have hnat : (4206819779 : ℕ)^4787*12500000000000^3763 ≤ 4154636327723^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206819779 10000000000 4154636327723 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1937760407/5000000000 : ℝ)^4787 ≤ (29943674445683/100000000000000 : ℝ)^3763 := by
    have hnat : (1937760407 : ℕ)^4787*100000000000000^3763 ≤ 29943674445683^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937760407 5000000000 29943674445683 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142477699/312500000 : ℝ)^4787 ≤ (36819234921503/100000000000000 : ℝ)^3763 := by
    have hnat : (142477699 : ℕ)^4787*100000000000000^3763 ≤ 36819234921503^3763*312500000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142477699 312500000 36819234921503 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206819779/10000000000 : ℝ), (1937760407/5000000000 : ℝ), (142477699/312500000 : ℝ)] ![(4154636327723/12500000000000 : ℝ), (29943674445683/100000000000000 : ℝ), (36819234921503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206819779/10000000000 : ℝ)|^4787 ≤ (4154636327723/12500000000000 : ℝ)^3763
        have hw : |(4206819779/10000000000 : ℝ)|=(4206819779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1937760407/5000000000 : ℝ)|^4787 ≤ (29943674445683/100000000000000 : ℝ)^3763
        have hw : |(1937760407/5000000000 : ℝ)|=(1937760407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142477699/312500000 : ℝ)|^4787 ≤ (36819234921503/100000000000000 : ℝ)^3763
        have hw : |(142477699/312500000 : ℝ)|=(142477699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210862613/1250000000 : ℝ)*x 0 + (5183580031/10000000000 : ℝ)*x 1 + (5455161271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210862613/1250000000 : ℝ)^4787 ≤ (5196759686251/50000000000000 : ℝ)^3763 := by
    have hnat : (210862613 : ℕ)^4787*50000000000000^3763 ≤ 5196759686251^3763*1250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210862613 1250000000 5196759686251 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183580031/10000000000 : ℝ)^4787 ≤ (173393941737/400000000000 : ℝ)^3763 := by
    have hnat : (5183580031 : ℕ)^4787*400000000000^3763 ≤ 173393941737^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183580031 10000000000 173393941737 400000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455161271/10000000000 : ℝ)^4787 ≤ (23128997594133/50000000000000 : ℝ)^3763 := by
    have hnat : (5455161271 : ℕ)^4787*50000000000000^3763 ≤ 23128997594133^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455161271 10000000000 23128997594133 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210862613/1250000000 : ℝ), (5183580031/10000000000 : ℝ), (5455161271/10000000000 : ℝ)] ![(5196759686251/50000000000000 : ℝ), (173393941737/400000000000 : ℝ), (23128997594133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210862613/1250000000 : ℝ)|^4787 ≤ (5196759686251/50000000000000 : ℝ)^3763
        have hw : |(-210862613/1250000000 : ℝ)|=(210862613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183580031/10000000000 : ℝ)|^4787 ≤ (173393941737/400000000000 : ℝ)^3763
        have hw : |(5183580031/10000000000 : ℝ)|=(5183580031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455161271/10000000000 : ℝ)|^4787 ≤ (23128997594133/50000000000000 : ℝ)^3763
        have hw : |(5455161271/10000000000 : ℝ)|=(5455161271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279236097/10000000000 : ℝ)*x 0 + (-1555319963/10000000000 : ℝ)*x 1 + (2727580643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279236097/10000000000 : ℝ)^4787 ≤ (44368649658163/100000000000000 : ℝ)^3763 := by
    have hnat : (5279236097 : ℕ)^4787*100000000000000^3763 ≤ 44368649658163^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279236097 10000000000 44368649658163 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1555319963/10000000000 : ℝ)^4787 ≤ (9373354966711/100000000000000 : ℝ)^3763 := by
    have hnat : (1555319963 : ℕ)^4787*100000000000000^3763 ≤ 9373354966711^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555319963 10000000000 9373354966711 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727580643/5000000000 : ℝ)^4787 ≤ (23128997675037/50000000000000 : ℝ)^3763 := by
    have hnat : (2727580643 : ℕ)^4787*50000000000000^3763 ≤ 23128997675037^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727580643 5000000000 23128997675037 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279236097/10000000000 : ℝ), (-1555319963/10000000000 : ℝ), (2727580643/5000000000 : ℝ)] ![(44368649658163/100000000000000 : ℝ), (9373354966711/100000000000000 : ℝ), (23128997675037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279236097/10000000000 : ℝ)|^4787 ≤ (44368649658163/100000000000000 : ℝ)^3763
        have hw : |(5279236097/10000000000 : ℝ)|=(5279236097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1555319963/10000000000 : ℝ)|^4787 ≤ (9373354966711/100000000000000 : ℝ)^3763
        have hw : |(-1555319963/10000000000 : ℝ)|=(1555319963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727580643/5000000000 : ℝ)|^4787 ≤ (23128997675037/50000000000000 : ℝ)^3763
        have hw : |(2727580643/5000000000 : ℝ)|=(2727580643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055847269/2000000000 : ℝ)*x 0 + (545516103/1000000000 : ℝ)*x 1 + (-1555319979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055847269/2000000000 : ℝ)^4787 ≤ (44368652309629/100000000000000 : ℝ)^3763 := by
    have hnat : (1055847269 : ℕ)^4787*100000000000000^3763 ≤ 44368652309629^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055847269 2000000000 44368652309629 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545516103/1000000000 : ℝ)^4787 ≤ (46257992588553/100000000000000 : ℝ)^3763 := by
    have hnat : (545516103 : ℕ)^4787*100000000000000^3763 ≤ 46257992588553^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545516103 1000000000 46257992588553 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1555319979/10000000000 : ℝ)^4787 ≤ (9373355089377/100000000000000 : ℝ)^3763 := by
    have hnat : (1555319979 : ℕ)^4787*100000000000000^3763 ≤ 9373355089377^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555319979 10000000000 9373355089377 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055847269/2000000000 : ℝ), (545516103/1000000000 : ℝ), (-1555319979/10000000000 : ℝ)] ![(44368652309629/100000000000000 : ℝ), (46257992588553/100000000000000 : ℝ), (9373355089377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055847269/2000000000 : ℝ)|^4787 ≤ (44368652309629/100000000000000 : ℝ)^3763
        have hw : |(1055847269/2000000000 : ℝ)|=(1055847269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545516103/1000000000 : ℝ)|^4787 ≤ (46257992588553/100000000000000 : ℝ)^3763
        have hw : |(545516103/1000000000 : ℝ)|=(545516103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1555319979/10000000000 : ℝ)|^4787 ≤ (9373355089377/100000000000000 : ℝ)^3763
        have hw : |(-1555319979/10000000000 : ℝ)|=(1555319979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_s5_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206990767/10000000000 : ℝ)*x 0 + (1138547979/2500000000 : ℝ)*x 1 + (970167247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206990767/10000000000 : ℝ)^4787 ≤ (33238809188267/100000000000000 : ℝ)^3763 := by
    have hnat : (4206990767 : ℕ)^4787*100000000000000^3763 ≤ 33238809188267^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206990767 10000000000 33238809188267 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138547979/2500000000 : ℝ)^4787 ≤ (7353381278587/20000000000000 : ℝ)^3763 := by
    have hnat : (1138547979 : ℕ)^4787*20000000000000^3763 ≤ 7353381278587^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138547979 2500000000 7353381278587 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970167247/2500000000 : ℝ)^4787 ≤ (14997142197807/50000000000000 : ℝ)^3763 := by
    have hnat : (970167247 : ℕ)^4787*50000000000000^3763 ≤ 14997142197807^3763*2500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970167247 2500000000 14997142197807 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206990767/10000000000 : ℝ), (1138547979/2500000000 : ℝ), (970167247/2500000000 : ℝ)] ![(33238809188267/100000000000000 : ℝ), (7353381278587/20000000000000 : ℝ), (14997142197807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206990767/10000000000 : ℝ)|^4787 ≤ (33238809188267/100000000000000 : ℝ)^3763
        have hw : |(4206990767/10000000000 : ℝ)|=(4206990767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1138547979/2500000000 : ℝ)|^4787 ≤ (7353381278587/20000000000000 : ℝ)^3763
        have hw : |(1138547979/2500000000 : ℝ)|=(1138547979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(970167247/2500000000 : ℝ)|^4787 ≤ (14997142197807/50000000000000 : ℝ)^3763
        have hw : |(970167247/2500000000 : ℝ)|=(970167247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (10481/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16329/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1633/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (131/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1633/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (131/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1633/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (131/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1633/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (131/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1633/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (131/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1633/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (131/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (131/1250 : ℝ) ^ (4783/1024 : ℝ) ≤ (331983927737413/12500000000000000000 : ℝ) := by
    have hpowers : (131/1250 : ℝ)^4783 ≤ (331983927737413/12500000000000000000 : ℝ)^1024 := by
      have hnat : (131 : ℕ)^4783*12500000000000000000^1024 ≤ 331983927737413^1024*1250^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 1250 331983927737413 12500000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/1250 : ℝ)) (X := (331983927737413/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1633/10000 : ℝ) ^ (4783/1024 : ℝ) ≤ (21083290849040837/100000000000000000000 : ℝ) := by
    have hpowers : (1633/10000 : ℝ)^4783 ≤ (21083290849040837/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1633 : ℕ)^4783*100000000000000000000^1024 ≤ 21083290849040837^1024*10000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1633 10000 21083290849040837 100000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1633/10000 : ℝ)) (X := (21083290849040837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250331983927737413/6250000000000000000 : ℝ) ≤ (312503553673913/312500000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (6250331983927737413/6250000000000000000 : ℝ)^1024 ≤ (312503553673913/312500000000000 : ℝ)^4783 := by
      have hnat : (6250331983927737413 : ℕ)^1024*312500000000000^4783 ≤ 312503553673913^4783*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250331983927737413 6250000000000000000 312503553673913 312500000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312503553673913/312500000000000 : ℝ)) (X := (6250331983927737413/6250000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100023739162270940141/100000000000000000000 : ℝ) ≤ (10000508188058819/10000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (100023739162270940141/100000000000000000000 : ℝ)^1024 ≤ (10000508188058819/10000000000000000 : ℝ)^4783 := by
      have hnat : (100023739162270940141 : ℕ)^1024*10000000000000000^4783 ≤ 10000508188058819^4783*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100023739162270940141 100000000000000000000 10000508188058819 10000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000508188058819/10000000000000000 : ℝ)) (X := (100023739162270940141/100000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021083290849040837/50000000000000000000 : ℝ) ≤ (5000451329276211/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (50021083290849040837/50000000000000000000 : ℝ)^1024 ≤ (5000451329276211/5000000000000000 : ℝ)^4783 := by
      have hnat : (50021083290849040837 : ℕ)^1024*5000000000000000^4783 ≤ 5000451329276211^4783*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021083290849040837 50000000000000000000 5000451329276211 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000451329276211/5000000000000000 : ℝ)) (X := (50021083290849040837/50000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(331983927737413/12500000000000000000 : ℝ) ≤ ((365577482163816217/365625000000000000 : ℝ)+2*(394470493603/585000000000000 : ℝ)*(131/1250 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (365577482163816217/365625000000000000 : ℝ)+2*(394470493603/585000000000000 : ℝ)*(131/1250 : ℝ)=(312503553673913/312500000000000 : ℝ) by norm_num, show 1+2*(331983927737413/12500000000000000000 : ℝ)=(6250331983927737413/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21083290849040837/100000000000000000000 : ℝ)+(331983927737413/12500000000000000000 : ℝ) ≤ ((365577482163816217/365625000000000000 : ℝ)+(394470493603/585000000000000 : ℝ)*((1633/10000 : ℝ)+(131/1250 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (365577482163816217/365625000000000000 : ℝ)+(394470493603/585000000000000 : ℝ)*((1633/10000 : ℝ)+(131/1250 : ℝ))=(10000508188058819/10000000000000000 : ℝ) by norm_num, show 1+(21083290849040837/100000000000000000000 : ℝ)+(331983927737413/12500000000000000000 : ℝ)=(100023739162270940141/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21083290849040837/100000000000000000000 : ℝ) ≤ ((365577482163816217/365625000000000000 : ℝ)+2*(394470493603/585000000000000 : ℝ)*(1633/10000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (365577482163816217/365625000000000000 : ℝ)+2*(394470493603/585000000000000 : ℝ)*(1633/10000 : ℝ)=(5000451329276211/5000000000000000 : ℝ) by norm_num, show 1+2*(21083290849040837/100000000000000000000 : ℝ)=(50021083290849040837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (365577482163816217/365625000000000000 : ℝ)*(X 1 0+X 2 0)+(394470493603/585000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (131/1250 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (365577482163816217/365625000000000000 : ℝ)) (alpha := (394470493603/585000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (365577482163816217/365625000000000000 : ℝ)*(X 0 1+X 2 1)+(394470493603/585000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (131/1250 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (365577482163816217/365625000000000000 : ℝ)) (alpha := (394470493603/585000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (365577482163816217/365625000000000000 : ℝ)*(X 0 2+X 1 2)+(394470493603/585000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (131/1250 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (365577482163816217/365625000000000000 : ℝ)) (alpha := (394470493603/585000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1686831937/10000000000 : ℝ)*X 0 0+(545723713/1000000000 : ℝ)*X 0 1+(1036305143/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338136901/2500000000 : ℝ)*X 1 0+(-45723883/250000000 : ℝ)*X 1 1+(5181525723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352547439/10000000000 : ℝ)*X 2 0+(5181525849/10000000000 : ℝ)*X 2 1+(-1828955373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206819779/10000000000 : ℝ)*X 0 0+(1937760407/5000000000 : ℝ)*X 0 1+(142477699/312500000 : ℝ)*X 0 2+(4206819779/10000000000 : ℝ)*X 1 0+(1937760407/5000000000 : ℝ)*X 1 1+(142477699/312500000 : ℝ)*X 1 2+(4206819779/10000000000 : ℝ)*X 2 0+(1937760407/5000000000 : ℝ)*X 2 1+(142477699/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210862613/1250000000 : ℝ)*X 0 0+(5183580031/10000000000 : ℝ)*X 0 1+(5455161271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279236097/10000000000 : ℝ)*X 1 0+(-1555319963/10000000000 : ℝ)*X 1 1+(2727580643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055847269/2000000000 : ℝ)*X 2 0+(545516103/1000000000 : ℝ)*X 2 1+(-1555319979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206990767/10000000000 : ℝ)*X 0 0+(1138547979/2500000000 : ℝ)*X 0 1+(970167247/2500000000 : ℝ)*X 0 2+(4206990767/10000000000 : ℝ)*X 1 0+(1138547979/2500000000 : ℝ)*X 1 1+(970167247/2500000000 : ℝ)*X 1 2+(4206990767/10000000000 : ℝ)*X 2 0+(1138547979/2500000000 : ℝ)*X 2 1+(970167247/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23138117708378731270747981/6093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189517111/25000000000000 : ℝ)*(base19) + (113729471/20000000000000 : ℝ)*(base23) + (41543073/100000000000000 : ℝ)*(lower2) + (156498491/100000000000000 : ℝ)*(upper3) + (42854967/100000000000000 : ℝ)*(upper5) + (2544747273849941/100000000000000 : ℝ)*(major0) + (2544747273849941/100000000000000 : ℝ)*(major1) + (2544747273849941/100000000000000 : ℝ)*(major2) + (725398171554943/20000000000000 : ℝ)*(sp0) + (453374729426609/12500000000000 : ℝ)*(sp1) + (90674950620849/2500000000000 : ℝ)*(sp2) + (29249844827987/2000000000000 : ℝ)*(sp3) + (7735706601/100000000000000 : ℝ)*(sp4) + (3586251727/100000000000000 : ℝ)*(sp7) + (731247913825539/50000000000000 : ℝ)*(f.failure) + (906749648370329/25000000000000 : ℝ)*(f.sum) + (186210538427423/29250000000000000000000000000 : ℝ)*base65 + (1098712001462693/351562500000000000000000000000 : ℝ)*base67 + (2679917688003511/703125000000000000000000000000 : ℝ)*base69 + (816595186885841/175781250000000000000000000000 : ℝ)*base72 + (154362471761423/29250000000000000000000000000 : ℝ)*base73 + (2996492434878511/703125000000000000000000000000 : ℝ)*base75 + (1534677708270409/175781250000000000000000000000 : ℝ)*base77 + (1366766570816011/703125000000000000000000000000 : ℝ)*base79 + (77145244544423/29250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2191709/500000000000000000000 : ℝ)*base89 + (2191709/500000000000000000000 : ℝ)*base91 + (2191709/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62767657106517634165622621/6093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1437027679/100000000000000 : ℝ)*(base19) + (1761278089/100000000000000 : ℝ)*(base23) + (92552403/20000000000000 : ℝ)*(lower1) + (97933537/50000000000000 : ℝ)*(upper3) + (70900027/100000000000000 : ℝ)*(lower4) + (55930447/25000000000000 : ℝ)*(upper5) + (2583423197361769/100000000000000 : ℝ)*(major0) + (2583423197361769/100000000000000 : ℝ)*(major1) + (2583423197361769/100000000000000 : ℝ)*(major2) + (1222573339/100000000000000 : ℝ)*(sp2) + (920530680270137/25000000000000 : ℝ)*(sp4) + (920530321013217/25000000000000 : ℝ)*(sp5) + (11506624178841/312500000000 : ℝ)*(sp6) + (371180832574633/25000000000000 : ℝ)*(sp7) + (371180832574633/25000000000000 : ℝ)*(f.failure) + (920530680270137/25000000000000 : ℝ)*(f.sum) + (66584639307293/29250000000000000000000000000 : ℝ)*base66 + (10251656832710101/703125000000000000000000000000 : ℝ)*base68 + (4143594365210101/703125000000000000000000000000 : ℝ)*base70 + (7850643821772601/703125000000000000000000000000 : ℝ)*base72 + (182228164005293/29250000000000000000000000000 : ℝ)*base74 + (14158881755102399/703125000000000000000000000000 : ℝ)*base75 + (1586910630612863/351562500000000000000000000000 : ℝ)*base78 + (629009524078997/87890625000000000000000000000 : ℝ)*base80 + (20361043110457/29250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1513623/250000000000000000000 : ℝ)*base89 + (1513623/250000000000000000000 : ℝ)*base91 + (1513623/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1617_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1617_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1617_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1617_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1617_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1617_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

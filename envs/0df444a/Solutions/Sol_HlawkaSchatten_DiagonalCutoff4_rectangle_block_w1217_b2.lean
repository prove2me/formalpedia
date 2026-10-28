-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:40.100907+00:00
-- url     : https://prove2.me/submissions/d492d52a-96a3-4ded-ab97-16c3844de115

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
theorem support_rectangle_w1217_s6_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131505793/10000000000 : ℝ)*x 0 + (5391887091/10000000000 : ℝ)*x 1 + (5266660931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131505793/10000000000 : ℝ)^4205 ≤ (6479673052899/50000000000000 : ℝ)^3181 := by
    have hnat : (2131505793 : ℕ)^4205*50000000000000^3181 ≤ 6479673052899^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131505793 10000000000 6479673052899 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391887091/10000000000 : ℝ)^4205 ≤ (4419621778283/10000000000000 : ℝ)^3181 := by
    have hnat : (5391887091 : ℕ)^4205*10000000000000^3181 ≤ 4419621778283^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391887091 10000000000 4419621778283 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266660931/10000000000 : ℝ)^4205 ≤ (42844436101279/100000000000000 : ℝ)^3181 := by
    have hnat : (5266660931 : ℕ)^4205*100000000000000^3181 ≤ 42844436101279^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266660931 10000000000 42844436101279 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131505793/10000000000 : ℝ), (5391887091/10000000000 : ℝ), (5266660931/10000000000 : ℝ)] ![(6479673052899/50000000000000 : ℝ), (4419621778283/10000000000000 : ℝ), (42844436101279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131505793/10000000000 : ℝ)|^4205 ≤ (6479673052899/50000000000000 : ℝ)^3181
        have hw : |(-2131505793/10000000000 : ℝ)|=(2131505793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391887091/10000000000 : ℝ)|^4205 ≤ (4419621778283/10000000000000 : ℝ)^3181
        have hw : |(5391887091/10000000000 : ℝ)|=(5391887091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266660931/10000000000 : ℝ)|^4205 ≤ (42844436101279/100000000000000 : ℝ)^3181
        have hw : |(5266660931/10000000000 : ℝ)|=(5266660931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344493717/10000000000 : ℝ)*x 0 + (-1097503897/5000000000 : ℝ)*x 1 + (2633330361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344493717/10000000000 : ℝ)^4205 ≤ (43683417578487/100000000000000 : ℝ)^3181 := by
    have hnat : (5344493717 : ℕ)^4205*100000000000000^3181 ≤ 43683417578487^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344493717 10000000000 43683417578487 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097503897/5000000000 : ℝ)^4205 ≤ (13472148544351/100000000000000 : ℝ)^3181 := by
    have hnat : (1097503897 : ℕ)^4205*100000000000000^3181 ≤ 13472148544351^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097503897 5000000000 13472148544351 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633330361/5000000000 : ℝ)^4205 ≤ (21422216926869/50000000000000 : ℝ)^3181 := by
    have hnat : (2633330361 : ℕ)^4205*50000000000000^3181 ≤ 21422216926869^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633330361 5000000000 21422216926869 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344493717/10000000000 : ℝ), (-1097503897/5000000000 : ℝ), (2633330361/5000000000 : ℝ)] ![(43683417578487/100000000000000 : ℝ), (13472148544351/100000000000000 : ℝ), (21422216926869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344493717/10000000000 : ℝ)|^4205 ≤ (43683417578487/100000000000000 : ℝ)^3181
        have hw : |(5344493717/10000000000 : ℝ)|=(5344493717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097503897/5000000000 : ℝ)|^4205 ≤ (13472148544351/100000000000000 : ℝ)^3181
        have hw : |(-1097503897/5000000000 : ℝ)|=(1097503897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633330361/5000000000 : ℝ)|^4205 ≤ (21422216926869/50000000000000 : ℝ)^3181
        have hw : |(2633330361/5000000000 : ℝ)|=(2633330361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344493599/10000000000 : ℝ)*x 0 + (5266660799/10000000000 : ℝ)*x 1 + (-43900157/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344493599/10000000000 : ℝ)^4205 ≤ (43683416303533/100000000000000 : ℝ)^3181 := by
    have hnat : (5344493599 : ℕ)^4205*100000000000000^3181 ≤ 43683416303533^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344493599 10000000000 43683416303533 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266660799/10000000000 : ℝ)^4205 ≤ (2142221734089/5000000000000 : ℝ)^3181 := by
    have hnat : (5266660799 : ℕ)^4205*5000000000000^3181 ≤ 2142221734089^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266660799 10000000000 2142221734089 5000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43900157/200000000 : ℝ)^4205 ≤ (13472148998701/100000000000000 : ℝ)^3181 := by
    have hnat : (43900157 : ℕ)^4205*100000000000000^3181 ≤ 13472148998701^3181*200000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43900157 200000000 13472148998701 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344493599/10000000000 : ℝ), (5266660799/10000000000 : ℝ), (-43900157/200000000 : ℝ)] ![(43683416303533/100000000000000 : ℝ), (2142221734089/5000000000000 : ℝ), (13472148998701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344493599/10000000000 : ℝ)|^4205 ≤ (43683416303533/100000000000000 : ℝ)^3181
        have hw : |(5344493599/10000000000 : ℝ)|=(5344493599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266660799/10000000000 : ℝ)|^4205 ≤ (2142221734089/5000000000000 : ℝ)^3181
        have hw : |(5266660799/10000000000 : ℝ)|=(5266660799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43900157/200000000 : ℝ)|^4205 ≤ (13472148998701/100000000000000 : ℝ)^3181
        have hw : |(-43900157/200000000 : ℝ)|=(43900157/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435420201/1000000000 : ℝ)*x 0 + (42295941/100000000 : ℝ)*x 1 + (560299861/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435420201/1000000000 : ℝ)^4205 ≤ (4164656234479/12500000000000 : ℝ)^3181 := by
    have hnat : (435420201 : ℕ)^4205*12500000000000^3181 ≤ 4164656234479^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435420201 1000000000 4164656234479 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42295941/100000000 : ℝ)^4205 ≤ (4007836650173/12500000000000 : ℝ)^3181 := by
    have hnat : (42295941 : ℕ)^4205*12500000000000^3181 ≤ 4007836650173^3181*100000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42295941 100000000 4007836650173 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560299861/1250000000 : ℝ)^4205 ≤ (17310028450639/50000000000000 : ℝ)^3181 := by
    have hnat : (560299861 : ℕ)^4205*50000000000000^3181 ≤ 17310028450639^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560299861 1250000000 17310028450639 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435420201/1000000000 : ℝ), (42295941/100000000 : ℝ), (560299861/1250000000 : ℝ)] ![(4164656234479/12500000000000 : ℝ), (4007836650173/12500000000000 : ℝ), (17310028450639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435420201/1000000000 : ℝ)|^4205 ≤ (4164656234479/12500000000000 : ℝ)^3181
        have hw : |(435420201/1000000000 : ℝ)|=(435420201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42295941/100000000 : ℝ)|^4205 ≤ (4007836650173/12500000000000 : ℝ)^3181
        have hw : |(42295941/100000000 : ℝ)|=(42295941/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560299861/1250000000 : ℝ)|^4205 ≤ (17310028450639/50000000000000 : ℝ)^3181
        have hw : |(560299861/1250000000 : ℝ)|=(560299861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53287767/250000000 : ℝ)*x 0 + (658372177/1250000000 : ℝ)*x 1 + (5391569359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53287767/250000000 : ℝ)^4205 ≤ (6479692691539/50000000000000 : ℝ)^3181 := by
    have hnat : (53287767 : ℕ)^4205*50000000000000^3181 ≤ 6479692691539^3181*250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53287767 250000000 6479692691539 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658372177/1250000000 : ℝ)^4205 ≤ (42847839546263/100000000000000 : ℝ)^3181 := by
    have hnat : (658372177 : ℕ)^4205*100000000000000^3181 ≤ 42847839546263^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658372177 1250000000 42847839546263 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391569359/10000000000 : ℝ)^4205 ≤ (44192775048709/100000000000000 : ℝ)^3181 := by
    have hnat : (5391569359 : ℕ)^4205*100000000000000^3181 ≤ 44192775048709^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391569359 10000000000 44192775048709 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53287767/250000000 : ℝ), (658372177/1250000000 : ℝ), (5391569359/10000000000 : ℝ)] ![(6479692691539/50000000000000 : ℝ), (42847839546263/100000000000000 : ℝ), (44192775048709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53287767/250000000 : ℝ)|^4205 ≤ (6479692691539/50000000000000 : ℝ)^3181
        have hw : |(-53287767/250000000 : ℝ)|=(53287767/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658372177/1250000000 : ℝ)|^4205 ≤ (42847839546263/100000000000000 : ℝ)^3181
        have hw : |(658372177/1250000000 : ℝ)|=(658372177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391569359/10000000000 : ℝ)|^4205 ≤ (44192775048709/100000000000000 : ℝ)^3181
        have hw : |(5391569359/10000000000 : ℝ)|=(5391569359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062519219/2000000000 : ℝ)*x 0 + (-2070099181/10000000000 : ℝ)*x 1 + (269578471/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062519219/2000000000 : ℝ)^4205 ≤ (43339105140047/100000000000000 : ℝ)^3181 := by
    have hnat : (1062519219 : ℕ)^4205*100000000000000^3181 ≤ 43339105140047^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062519219 2000000000 43339105140047 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070099181/10000000000 : ℝ)^4205 ≤ (12468119132571/100000000000000 : ℝ)^3181 := by
    have hnat : (2070099181 : ℕ)^4205*100000000000000^3181 ≤ 12468119132571^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070099181 10000000000 12468119132571 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269578471/500000000 : ℝ)^4205 ≤ (22096387854829/50000000000000 : ℝ)^3181 := by
    have hnat : (269578471 : ℕ)^4205*50000000000000^3181 ≤ 22096387854829^3181*500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269578471 500000000 22096387854829 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062519219/2000000000 : ℝ), (-2070099181/10000000000 : ℝ), (269578471/500000000 : ℝ)] ![(43339105140047/100000000000000 : ℝ), (12468119132571/100000000000000 : ℝ), (22096387854829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062519219/2000000000 : ℝ)|^4205 ≤ (43339105140047/100000000000000 : ℝ)^3181
        have hw : |(1062519219/2000000000 : ℝ)|=(1062519219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070099181/10000000000 : ℝ)|^4205 ≤ (12468119132571/100000000000000 : ℝ)^3181
        have hw : |(-2070099181/10000000000 : ℝ)|=(2070099181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269578471/500000000 : ℝ)|^4205 ≤ (22096387854829/50000000000000 : ℝ)^3181
        have hw : |(269578471/500000000 : ℝ)|=(269578471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312596039/10000000000 : ℝ)*x 0 + (5391569467/10000000000 : ℝ)*x 1 + (-2070099193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312596039/10000000000 : ℝ)^4205 ≤ (43339104536149/100000000000000 : ℝ)^3181 := by
    have hnat : (5312596039 : ℕ)^4205*100000000000000^3181 ≤ 43339104536149^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312596039 10000000000 43339104536149 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391569467/10000000000 : ℝ)^4205 ≤ (22096388109457/50000000000000 : ℝ)^3181 := by
    have hnat : (5391569467 : ℕ)^4205*50000000000000^3181 ≤ 22096388109457^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391569467 10000000000 22096388109457 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070099193/10000000000 : ℝ)^4205 ≤ (12468119228113/100000000000000 : ℝ)^3181 := by
    have hnat : (2070099193 : ℕ)^4205*100000000000000^3181 ≤ 12468119228113^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070099193 10000000000 12468119228113 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312596039/10000000000 : ℝ), (5391569467/10000000000 : ℝ), (-2070099193/10000000000 : ℝ)] ![(43339104536149/100000000000000 : ℝ), (22096388109457/50000000000000 : ℝ), (12468119228113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312596039/10000000000 : ℝ)|^4205 ≤ (43339104536149/100000000000000 : ℝ)^3181
        have hw : |(5312596039/10000000000 : ℝ)|=(5312596039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391569467/10000000000 : ℝ)|^4205 ≤ (22096388109457/50000000000000 : ℝ)^3181
        have hw : |(5391569467/10000000000 : ℝ)|=(5391569467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070099193/10000000000 : ℝ)|^4205 ≤ (12468119228113/100000000000000 : ℝ)^3181
        have hw : |(-2070099193/10000000000 : ℝ)|=(2070099193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s6_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354211913/10000000000 : ℝ)*x 0 + (4481759597/10000000000 : ℝ)*x 1 + (132194857/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354211913/10000000000 : ℝ)^4205 ≤ (1332694001761/4000000000000 : ℝ)^3181 := by
    have hnat : (4354211913 : ℕ)^4205*4000000000000^3181 ≤ 1332694001761^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354211913 10000000000 1332694001761 4000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481759597/10000000000 : ℝ)^4205 ≤ (17306764991109/50000000000000 : ℝ)^3181 := by
    have hnat : (4481759597 : ℕ)^4205*50000000000000^3181 ≤ 17306764991109^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481759597 10000000000 17306764991109 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132194857/312500000 : ℝ)^4205 ≤ (32069119956177/100000000000000 : ℝ)^3181 := by
    have hnat : (132194857 : ℕ)^4205*100000000000000^3181 ≤ 32069119956177^3181*312500000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132194857 312500000 32069119956177 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354211913/10000000000 : ℝ), (4481759597/10000000000 : ℝ), (132194857/312500000 : ℝ)] ![(1332694001761/4000000000000 : ℝ), (17306764991109/50000000000000 : ℝ), (32069119956177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354211913/10000000000 : ℝ)|^4205 ≤ (1332694001761/4000000000000 : ℝ)^3181
        have hw : |(4354211913/10000000000 : ℝ)|=(4354211913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481759597/10000000000 : ℝ)|^4205 ≤ (17306764991109/50000000000000 : ℝ)^3181
        have hw : |(4481759597/10000000000 : ℝ)|=(4481759597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132194857/312500000 : ℝ)|^4205 ≤ (32069119956177/100000000000000 : ℝ)^3181
        have hw : |(132194857/312500000 : ℝ)|=(132194857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11443/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11421/100000 : ℝ) ^ (8409/2048 : ℝ) ≤ (13519905416680359/100000000000000000000 : ℝ) := by
    have hpowers : (11421/100000 : ℝ)^8409 ≤ (13519905416680359/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11421 : ℕ)^8409*100000000000000000000^2048 ≤ 13519905416680359^2048*100000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11421 100000 13519905416680359 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11421/100000 : ℝ)) (X := (13519905416680359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (8409/2048 : ℝ) ≤ (403801388779467/1250000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^8409 ≤ (403801388779467/1250000000000000000 : ℝ)^2048 := by
      have hnat : (353 : ℕ)^8409*1250000000000000000^2048 ≤ 403801388779467^2048*2500^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 403801388779467 1250000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (403801388779467/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013519905416680359/50000000000000000000 : ℝ) ≤ (5000329241704953/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50013519905416680359/50000000000000000000 : ℝ)^2048 ≤ (5000329241704953/5000000000000000 : ℝ)^8409 := by
      have hnat : (50013519905416680359 : ℕ)^2048*5000000000000000^8409 ≤ 5000329241704953^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013519905416680359 50000000000000000000 5000329241704953 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329241704953/5000000000000000 : ℝ)) (X := (50013519905416680359/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045824016519037719/100000000000000000000 : ℝ) ≤ (5000557922016279/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100045824016519037719/100000000000000000000 : ℝ)^2048 ≤ (5000557922016279/5000000000000000 : ℝ)^8409 := by
      have hnat : (100045824016519037719 : ℕ)^2048*5000000000000000^8409 ≤ 5000557922016279^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045824016519037719 100000000000000000000 5000557922016279 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000557922016279/5000000000000000 : ℝ)) (X := (100045824016519037719/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (625403801388779467/625000000000000000 : ℝ) ≤ (1000157320465521/1000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (625403801388779467/625000000000000000 : ℝ)^2048 ≤ (1000157320465521/1000000000000000 : ℝ)^8409 := by
      have hnat : (625403801388779467 : ℕ)^2048*1000000000000000^8409 ≤ 1000157320465521^8409*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625403801388779467 625000000000000000 1000157320465521 1000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000157320465521/1000000000000000 : ℝ)) (X := (625403801388779467/625000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13519905416680359/100000000000000000000 : ℝ) ≤ ((2698133021538071931/2699000000000000000 : ℝ)+2*(114340155663/67475000000000 : ℝ)*(11421/100000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (2698133021538071931/2699000000000000000 : ℝ)+2*(114340155663/67475000000000 : ℝ)*(11421/100000 : ℝ)=(5000329241704953/5000000000000000 : ℝ) by norm_num, show 1+2*(13519905416680359/100000000000000000000 : ℝ)=(50013519905416680359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(403801388779467/1250000000000000000 : ℝ)+(13519905416680359/100000000000000000000 : ℝ) ≤ ((2698133021538071931/2699000000000000000 : ℝ)+(114340155663/67475000000000 : ℝ)*((353/2500 : ℝ)+(11421/100000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (2698133021538071931/2699000000000000000 : ℝ)+(114340155663/67475000000000 : ℝ)*((353/2500 : ℝ)+(11421/100000 : ℝ))=(5000557922016279/5000000000000000 : ℝ) by norm_num, show 1+(403801388779467/1250000000000000000 : ℝ)+(13519905416680359/100000000000000000000 : ℝ)=(100045824016519037719/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(403801388779467/1250000000000000000 : ℝ) ≤ ((2698133021538071931/2699000000000000000 : ℝ)+2*(114340155663/67475000000000 : ℝ)*(353/2500 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (2698133021538071931/2699000000000000000 : ℝ)+2*(114340155663/67475000000000 : ℝ)*(353/2500 : ℝ)=(1000157320465521/1000000000000000 : ℝ) by norm_num, show 1+2*(403801388779467/1250000000000000000 : ℝ)=(625403801388779467/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2698133021538071931/2699000000000000000 : ℝ)*(X 1 0+X 2 0)+(114340155663/67475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (2698133021538071931/2699000000000000000 : ℝ)) (alpha := (114340155663/67475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2698133021538071931/2699000000000000000 : ℝ)*(X 0 1+X 2 1)+(114340155663/67475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (2698133021538071931/2699000000000000000 : ℝ)) (alpha := (114340155663/67475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2698133021538071931/2699000000000000000 : ℝ)*(X 0 2+X 1 2)+(114340155663/67475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (2698133021538071931/2699000000000000000 : ℝ)) (alpha := (114340155663/67475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131505793/10000000000 : ℝ)*X 0 0+(5391887091/10000000000 : ℝ)*X 0 1+(5266660931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344493717/10000000000 : ℝ)*X 1 0+(-1097503897/5000000000 : ℝ)*X 1 1+(2633330361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344493599/10000000000 : ℝ)*X 2 0+(5266660799/10000000000 : ℝ)*X 2 1+(-43900157/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435420201/1000000000 : ℝ)*X 0 0+(42295941/100000000 : ℝ)*X 0 1+(560299861/1250000000 : ℝ)*X 0 2+(435420201/1000000000 : ℝ)*X 1 0+(42295941/100000000 : ℝ)*X 1 1+(560299861/1250000000 : ℝ)*X 1 2+(435420201/1000000000 : ℝ)*X 2 0+(42295941/100000000 : ℝ)*X 2 1+(560299861/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53287767/250000000 : ℝ)*X 0 0+(658372177/1250000000 : ℝ)*X 0 1+(5391569359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062519219/2000000000 : ℝ)*X 1 0+(-2070099181/10000000000 : ℝ)*X 1 1+(269578471/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312596039/10000000000 : ℝ)*X 2 0+(5391569467/10000000000 : ℝ)*X 2 1+(-2070099193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354211913/10000000000 : ℝ)*X 0 0+(4481759597/10000000000 : ℝ)*X 0 1+(132194857/312500000 : ℝ)*X 0 2+(4354211913/10000000000 : ℝ)*X 1 0+(4481759597/10000000000 : ℝ)*X 1 1+(132194857/312500000 : ℝ)*X 1 2+(4354211913/10000000000 : ℝ)*X 2 0+(4481759597/10000000000 : ℝ)*X 2 1+(132194857/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286566534058636546119599061/26990000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (888376349/50000000000000 : ℝ)*(base19) + (733903341/50000000000000 : ℝ)*(base23) + (70885553/100000000000000 : ℝ)*(lower2) + (234435873/100000000000000 : ℝ)*(upper3) + (14148429/100000000000000 : ℝ)*(upper5) + (1194130084831077/20000000000000 : ℝ)*(major0) + (1194130084831077/20000000000000 : ℝ)*(major1) + (1194130084831077/20000000000000 : ℝ)*(major2) + (3992798872452807/50000000000000 : ℝ)*(sp0) + (1597126233375449/20000000000000 : ℝ)*(sp1) + (7985631475823261/100000000000000 : ℝ)*(sp2) + (1977821110920357/50000000000000 : ℝ)*(sp3) + (35198724329/100000000000000 : ℝ)*(sp4) + (12664461591/50000000000000 : ℝ)*(sp7) + (494458443845487/12500000000000 : ℝ)*(f.failure) + (7985632943629943/100000000000000 : ℝ)*(f.sum) + (706628757011/337375000000000000000000000 : ℝ)*base65 + (691921416160079687/53980000000000000000000000000000 : ℝ)*base67 + (433776378518860313/53980000000000000000000000000000 : ℝ)*base70 + (423366067022340313/53980000000000000000000000000000 : ℝ)*base72 + (849952166183/168687500000000000000000000 : ℝ)*base73 + (108626182965960313/53980000000000000000000000000000 : ℝ)*base76 + (275300906684860313/53980000000000000000000000000000 : ℝ)*base78 + (99854590162099687/53980000000000000000000000000000 : ℝ)*base79 + (8623994468777/1349500000000000000000000000 : ℝ)*base81 + (399351/39062500000000000000 : ℝ)*base89 + (399351/39062500000000000000 : ℝ)*base91 + (399351/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (347370653114603232509853687/67475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (931076697/100000000000000 : ℝ)*(base19) + (950570831/100000000000000 : ℝ)*(base23) + (556387/390625000000 : ℝ)*(upper3) + (365531/781250000000 : ℝ)*(lower4) + (5321347/5000000000000 : ℝ)*(upper5) + (6000979141368359/100000000000000 : ℝ)*(major0) + (6000979141368359/100000000000000 : ℝ)*(major1) + (6000979141368359/100000000000000 : ℝ)*(major2) + (26868021927/100000000000000 : ℝ)*(sp1) + (29537612329/100000000000000 : ℝ)*(sp2) + (1003274652262513/12500000000000 : ℝ)*(sp4) + (8026169419001479/100000000000000 : ℝ)*(sp5) + (1605233345983389/20000000000000 : ℝ)*(sp6) + (248485055814499/6250000000000 : ℝ)*(sp7) + (248485055814499/6250000000000 : ℝ)*(f.failure) + (1003274652262513/12500000000000 : ℝ)*(f.sum) + (2673357007643/3373750000000000000000000000 : ℝ)*base66 + (1862905306521311229/269900000000000000000000000000000 : ℝ)*base67 + (2489100708994688771/269900000000000000000000000000000 : ℝ)*base70 + (3366671923274288771/269900000000000000000000000000000 : ℝ)*base72 + (48163016683123/13495000000000000000000000000 : ℝ)*base73 + (48046875240888771/269900000000000000000000000000000 : ℝ)*base76 + (1662416918438088771/269900000000000000000000000000000 : ℝ)*base78 + (3836318726626488771/269900000000000000000000000000000 : ℝ)*base80 + (35399784009527/13495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (723929/39062500000000000000 : ℝ)*base89 + (723929/39062500000000000000 : ℝ)*base91 + (723929/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_s7_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131527717/10000000000 : ℝ)*x 0 + (336979061/625000000 : ℝ)*x 1 + (658358543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131527717/10000000000 : ℝ)^4205 ≤ (161994028891/1250000000000 : ℝ)^3181 := by
    have hnat : (2131527717 : ℕ)^4205*1250000000000^3181 ≤ 161994028891^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131527717 10000000000 161994028891 1250000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336979061/625000000 : ℝ)^4205 ≤ (8838762216901/20000000000000 : ℝ)^3181 := by
    have hnat : (336979061 : ℕ)^4205*20000000000000^3181 ≤ 8838762216901^3181*625000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336979061 625000000 8838762216901 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658358543/1250000000 : ℝ)^4205 ≤ (42846666590501/100000000000000 : ℝ)^3181 := by
    have hnat : (658358543 : ℕ)^4205*100000000000000^3181 ≤ 42846666590501^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658358543 1250000000 42846666590501 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131527717/10000000000 : ℝ), (336979061/625000000 : ℝ), (658358543/1250000000 : ℝ)] ![(161994028891/1250000000000 : ℝ), (8838762216901/20000000000000 : ℝ), (42846666590501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131527717/10000000000 : ℝ)|^4205 ≤ (161994028891/1250000000000 : ℝ)^3181
        have hw : |(-2131527717/10000000000 : ℝ)|=(2131527717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336979061/625000000 : ℝ)|^4205 ≤ (8838762216901/20000000000000 : ℝ)^3181
        have hw : |(336979061/625000000 : ℝ)|=(336979061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658358543/1250000000 : ℝ)|^4205 ≤ (42846666590501/100000000000000 : ℝ)^3181
        have hw : |(658358543/1250000000 : ℝ)|=(658358543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672218297/5000000000 : ℝ)*x 0 + (-2194808671/10000000000 : ℝ)*x 1 + (658358543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672218297/5000000000 : ℝ)^4205 ≤ (1092070009579/2500000000000 : ℝ)^3181 := by
    have hnat : (2672218297 : ℕ)^4205*2500000000000^3181 ≤ 1092070009579^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672218297 5000000000 1092070009579 2500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194808671/10000000000 : ℝ)^4205 ≤ (6735266501251/50000000000000 : ℝ)^3181 := by
    have hnat : (2194808671 : ℕ)^4205*50000000000000^3181 ≤ 6735266501251^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194808671 10000000000 6735266501251 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658358543/1250000000 : ℝ)^4205 ≤ (42846666590501/100000000000000 : ℝ)^3181 := by
    have hnat : (658358543 : ℕ)^4205*100000000000000^3181 ≤ 42846666590501^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658358543 1250000000 42846666590501 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672218297/5000000000 : ℝ), (-2194808671/10000000000 : ℝ), (658358543/1250000000 : ℝ)] ![(1092070009579/2500000000000 : ℝ), (6735266501251/50000000000000 : ℝ), (42846666590501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672218297/5000000000 : ℝ)|^4205 ≤ (1092070009579/2500000000000 : ℝ)^3181
        have hw : |(2672218297/5000000000 : ℝ)|=(2672218297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194808671/10000000000 : ℝ)|^4205 ≤ (6735266501251/50000000000000 : ℝ)^3181
        have hw : |(-2194808671/10000000000 : ℝ)|=(2194808671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658358543/1250000000 : ℝ)|^4205 ≤ (42846666590501/100000000000000 : ℝ)^3181
        have hw : |(658358543/1250000000 : ℝ)|=(658358543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068887319/2000000000 : ℝ)*x 0 + (658358543/1250000000 : ℝ)*x 1 + (-68587771/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068887319/2000000000 : ℝ)^4205 ≤ (8736560078793/20000000000000 : ℝ)^3181 := by
    have hnat : (1068887319 : ℕ)^4205*20000000000000^3181 ≤ 8736560078793^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068887319 2000000000 8736560078793 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658358543/1250000000 : ℝ)^4205 ≤ (42846666590501/100000000000000 : ℝ)^3181 := by
    have hnat : (658358543 : ℕ)^4205*100000000000000^3181 ≤ 42846666590501^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658358543 1250000000 42846666590501 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68587771/312500000 : ℝ)^4205 ≤ (2694106602123/20000000000000 : ℝ)^3181 := by
    have hnat : (68587771 : ℕ)^4205*20000000000000^3181 ≤ 2694106602123^3181*312500000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68587771 312500000 2694106602123 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068887319/2000000000 : ℝ), (658358543/1250000000 : ℝ), (-68587771/312500000 : ℝ)] ![(8736560078793/20000000000000 : ℝ), (42846666590501/100000000000000 : ℝ), (2694106602123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068887319/2000000000 : ℝ)|^4205 ≤ (8736560078793/20000000000000 : ℝ)^3181
        have hw : |(1068887319/2000000000 : ℝ)|=(1068887319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658358543/1250000000 : ℝ)|^4205 ≤ (42846666590501/100000000000000 : ℝ)^3181
        have hw : |(658358543/1250000000 : ℝ)|=(658358543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68587771/312500000 : ℝ)|^4205 ≤ (2694106602123/20000000000000 : ℝ)^3181
        have hw : |(-68587771/312500000 : ℝ)|=(68587771/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177106563/5000000000 : ℝ)*x 0 + (211501317/500000000 : ℝ)*x 1 + (560245453/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177106563/5000000000 : ℝ)^4205 ≤ (6663472462689/20000000000000 : ℝ)^3181 := by
    have hnat : (2177106563 : ℕ)^4205*20000000000000^3181 ≤ 6663472462689^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177106563 5000000000 6663472462689 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211501317/500000000 : ℝ)^4205 ≤ (32067024675633/100000000000000 : ℝ)^3181 := by
    have hnat : (211501317 : ℕ)^4205*100000000000000^3181 ≤ 32067024675633^3181*500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211501317 500000000 32067024675633 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560245453/1250000000 : ℝ)^4205 ≤ (34615612988079/100000000000000 : ℝ)^3181 := by
    have hnat : (560245453 : ℕ)^4205*100000000000000^3181 ≤ 34615612988079^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560245453 1250000000 34615612988079 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177106563/5000000000 : ℝ), (211501317/500000000 : ℝ), (560245453/1250000000 : ℝ)] ![(6663472462689/20000000000000 : ℝ), (32067024675633/100000000000000 : ℝ), (34615612988079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177106563/5000000000 : ℝ)|^4205 ≤ (6663472462689/20000000000000 : ℝ)^3181
        have hw : |(2177106563/5000000000 : ℝ)|=(2177106563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211501317/500000000 : ℝ)|^4205 ≤ (32067024675633/100000000000000 : ℝ)^3181
        have hw : |(211501317/500000000 : ℝ)|=(211501317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560245453/1250000000 : ℝ)|^4205 ≤ (34615612988079/100000000000000 : ℝ)^3181
        have hw : |(560245453/1250000000 : ℝ)|=(560245453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213153243/1000000000 : ℝ)*x 0 + (329198923/625000000 : ℝ)*x 1 + (1347837353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213153243/1000000000 : ℝ)^4205 ≤ (1295956019023/10000000000000 : ℝ)^3181 := by
    have hnat : (213153243 : ℕ)^4205*10000000000000^3181 ≤ 1295956019023^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213153243 1000000000 1295956019023 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329198923/625000000 : ℝ)^4205 ≤ (334765999331/781250000000 : ℝ)^3181 := by
    have hnat : (329198923 : ℕ)^4205*781250000000^3181 ≤ 334765999331^3181*625000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329198923 625000000 334765999331 781250000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347837353/2500000000 : ℝ)^4205 ≤ (44190391886523/100000000000000 : ℝ)^3181 := by
    have hnat : (1347837353 : ℕ)^4205*100000000000000^3181 ≤ 44190391886523^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347837353 2500000000 44190391886523 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213153243/1000000000 : ℝ), (329198923/625000000 : ℝ), (1347837353/2500000000 : ℝ)] ![(1295956019023/10000000000000 : ℝ), (334765999331/781250000000 : ℝ), (44190391886523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213153243/1000000000 : ℝ)|^4205 ≤ (1295956019023/10000000000000 : ℝ)^3181
        have hw : |(-213153243/1000000000 : ℝ)|=(213153243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329198923/625000000 : ℝ)|^4205 ≤ (334765999331/781250000000 : ℝ)^3181
        have hw : |(329198923/625000000 : ℝ)|=(329198923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347837353/2500000000 : ℝ)|^4205 ≤ (44190391886523/100000000000000 : ℝ)^3181
        have hw : |(1347837353/2500000000 : ℝ)|=(1347837353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312648501/10000000000 : ℝ)*x 0 + (-414065521/2000000000 : ℝ)*x 1 + (539134941/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312648501/10000000000 : ℝ)^4205 ≤ (43339670281513/100000000000000 : ℝ)^3181 := by
    have hnat : (5312648501 : ℕ)^4205*100000000000000^3181 ≤ 43339670281513^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312648501 10000000000 43339670281513 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414065521/2000000000 : ℝ)^4205 ≤ (6234968917331/50000000000000 : ℝ)^3181 := by
    have hnat : (414065521 : ℕ)^4205*50000000000000^3181 ≤ 6234968917331^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414065521 2000000000 6234968917331 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539134941/1000000000 : ℝ)^4205 ≤ (44190391864853/100000000000000 : ℝ)^3181 := by
    have hnat : (539134941 : ℕ)^4205*100000000000000^3181 ≤ 44190391864853^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539134941 1000000000 44190391864853 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312648501/10000000000 : ℝ), (-414065521/2000000000 : ℝ), (539134941/1000000000 : ℝ)] ![(43339670281513/100000000000000 : ℝ), (6234968917331/50000000000000 : ℝ), (44190391864853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312648501/10000000000 : ℝ)|^4205 ≤ (43339670281513/100000000000000 : ℝ)^3181
        have hw : |(5312648501/10000000000 : ℝ)|=(5312648501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414065521/2000000000 : ℝ)|^4205 ≤ (6234968917331/50000000000000 : ℝ)^3181
        have hw : |(-414065521/2000000000 : ℝ)|=(414065521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539134941/1000000000 : ℝ)|^4205 ≤ (44190391864853/100000000000000 : ℝ)^3181
        have hw : |(539134941/1000000000 : ℝ)|=(539134941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312648501/10000000000 : ℝ)*x 0 + (1347837353/2500000000 : ℝ)*x 1 + (-2070327603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312648501/10000000000 : ℝ)^4205 ≤ (43339670281513/100000000000000 : ℝ)^3181 := by
    have hnat : (5312648501 : ℕ)^4205*100000000000000^3181 ≤ 43339670281513^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312648501 10000000000 43339670281513 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347837353/2500000000 : ℝ)^4205 ≤ (44190391886523/100000000000000 : ℝ)^3181 := by
    have hnat : (1347837353 : ℕ)^4205*100000000000000^3181 ≤ 44190391886523^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347837353 2500000000 44190391886523 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070327603/10000000000 : ℝ)^4205 ≤ (6234968909369/50000000000000 : ℝ)^3181 := by
    have hnat : (2070327603 : ℕ)^4205*50000000000000^3181 ≤ 6234968909369^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070327603 10000000000 6234968909369 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312648501/10000000000 : ℝ), (1347837353/2500000000 : ℝ), (-2070327603/10000000000 : ℝ)] ![(43339670281513/100000000000000 : ℝ), (44190391886523/100000000000000 : ℝ), (6234968909369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312648501/10000000000 : ℝ)|^4205 ≤ (43339670281513/100000000000000 : ℝ)^3181
        have hw : |(5312648501/10000000000 : ℝ)|=(5312648501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347837353/2500000000 : ℝ)|^4205 ≤ (44190391886523/100000000000000 : ℝ)^3181
        have hw : |(1347837353/2500000000 : ℝ)|=(1347837353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070327603/10000000000 : ℝ)|^4205 ≤ (6234968909369/50000000000000 : ℝ)^3181
        have hw : |(-2070327603/10000000000 : ℝ)|=(2070327603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s7_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177111317/5000000000 : ℝ)*x 0 + (35850631/80000000 : ℝ)*x 1 + (2115331697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177111317/5000000000 : ℝ)^4205 ≤ (33317458486317/100000000000000 : ℝ)^3181 := by
    have hnat : (2177111317 : ℕ)^4205*100000000000000^3181 ≤ 33317458486317^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177111317 5000000000 33317458486317 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35850631/80000000 : ℝ)^4205 ≤ (34609132642661/100000000000000 : ℝ)^3181 := by
    have hnat : (35850631 : ℕ)^4205*100000000000000^3181 ≤ 34609132642661^3181*80000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35850631 80000000 34609132642661 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115331697/5000000000 : ℝ)^4205 ≤ (32073408849399/100000000000000 : ℝ)^3181 := by
    have hnat : (2115331697 : ℕ)^4205*100000000000000^3181 ≤ 32073408849399^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115331697 5000000000 32073408849399 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177111317/5000000000 : ℝ), (35850631/80000000 : ℝ), (2115331697/5000000000 : ℝ)] ![(33317458486317/100000000000000 : ℝ), (34609132642661/100000000000000 : ℝ), (32073408849399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177111317/5000000000 : ℝ)|^4205 ≤ (33317458486317/100000000000000 : ℝ)^3181
        have hw : |(2177111317/5000000000 : ℝ)|=(2177111317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35850631/80000000 : ℝ)|^4205 ≤ (34609132642661/100000000000000 : ℝ)^3181
        have hw : |(35850631/80000000 : ℝ)|=(35850631/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115331697/5000000000 : ℝ)|^4205 ≤ (32073408849399/100000000000000 : ℝ)^3181
        have hw : |(2115331697/5000000000 : ℝ)|=(2115331697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1431/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11443/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11443/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11443/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11443/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11443/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11443/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11443/100000 : ℝ) ^ (8409/2048 : ℝ) ≤ (545086298577337/4000000000000000000 : ℝ) := by
    have hpowers : (11443/100000 : ℝ)^8409 ≤ (545086298577337/4000000000000000000 : ℝ)^2048 := by
      have hnat : (11443 : ℕ)^8409*4000000000000000000^2048 ≤ 545086298577337^2048*100000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11443 100000 545086298577337 4000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11443/100000 : ℝ)) (X := (545086298577337/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (881/6250 : ℝ) ^ (8409/2048 : ℝ) ≤ (16039628135985419/50000000000000000000 : ℝ) := by
    have hpowers : (881/6250 : ℝ)^8409 ≤ (16039628135985419/50000000000000000000 : ℝ)^2048 := by
      have hnat : (881 : ℕ)^8409*50000000000000000000^2048 ≤ 16039628135985419^2048*6250^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        881 6250 16039628135985419 50000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (881/6250 : ℝ)) (X := (16039628135985419/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000545086298577337/2000000000000000000 : ℝ) ≤ (10000663706554109/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (2000545086298577337/2000000000000000000 : ℝ)^2048 ≤ (10000663706554109/10000000000000000 : ℝ)^8409 := by
      have hnat : (2000545086298577337 : ℕ)^2048*10000000000000000^8409 ≤ 10000663706554109^8409*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000545086298577337 2000000000000000000 10000663706554109 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000663706554109/10000000000000000 : ℝ)) (X := (2000545086298577337/2000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045706413736404263/100000000000000000000 : ℝ) ≤ (5000556490412331/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100045706413736404263/100000000000000000000 : ℝ)^2048 ≤ (5000556490412331/5000000000000000 : ℝ)^8409 := by
      have hnat : (100045706413736404263 : ℕ)^2048*5000000000000000^8409 ≤ 5000556490412331^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045706413736404263 100000000000000000000 5000556490412331 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000556490412331/5000000000000000 : ℝ)) (X := (100045706413736404263/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016039628135985419/25000000000000000000 : ℝ) ≤ (2000312451019043/2000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (25016039628135985419/25000000000000000000 : ℝ)^2048 ≤ (2000312451019043/2000000000000000 : ℝ)^8409 := by
      have hnat : (25016039628135985419 : ℕ)^2048*2000000000000000^8409 ≤ 2000312451019043^8409*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016039628135985419 25000000000000000000 2000312451019043 2000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000312451019043/2000000000000000 : ℝ)) (X := (25016039628135985419/25000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(545086298577337/4000000000000000000 : ℝ) ≤ ((26521478722532175219/26530000000000000000 : ℝ)+2*(449274270553/265300000000000 : ℝ)*(11443/100000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (26521478722532175219/26530000000000000000 : ℝ)+2*(449274270553/265300000000000 : ℝ)*(11443/100000 : ℝ)=(10000663706554109/10000000000000000 : ℝ) by norm_num, show 1+2*(545086298577337/4000000000000000000 : ℝ)=(2000545086298577337/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16039628135985419/50000000000000000000 : ℝ)+(545086298577337/4000000000000000000 : ℝ) ≤ ((26521478722532175219/26530000000000000000 : ℝ)+(449274270553/265300000000000 : ℝ)*((881/6250 : ℝ)+(11443/100000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (26521478722532175219/26530000000000000000 : ℝ)+(449274270553/265300000000000 : ℝ)*((881/6250 : ℝ)+(11443/100000 : ℝ))=(5000556490412331/5000000000000000 : ℝ) by norm_num, show 1+(16039628135985419/50000000000000000000 : ℝ)+(545086298577337/4000000000000000000 : ℝ)=(100045706413736404263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16039628135985419/50000000000000000000 : ℝ) ≤ ((26521478722532175219/26530000000000000000 : ℝ)+2*(449274270553/265300000000000 : ℝ)*(881/6250 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (26521478722532175219/26530000000000000000 : ℝ)+2*(449274270553/265300000000000 : ℝ)*(881/6250 : ℝ)=(2000312451019043/2000000000000000 : ℝ) by norm_num, show 1+2*(16039628135985419/50000000000000000000 : ℝ)=(25016039628135985419/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26521478722532175219/26530000000000000000 : ℝ)*(X 1 0+X 2 0)+(449274270553/265300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11443/100000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (26521478722532175219/26530000000000000000 : ℝ)) (alpha := (449274270553/265300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26521478722532175219/26530000000000000000 : ℝ)*(X 0 1+X 2 1)+(449274270553/265300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11443/100000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (26521478722532175219/26530000000000000000 : ℝ)) (alpha := (449274270553/265300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26521478722532175219/26530000000000000000 : ℝ)*(X 0 2+X 1 2)+(449274270553/265300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (11443/100000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (26521478722532175219/26530000000000000000 : ℝ)) (alpha := (449274270553/265300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131527717/10000000000 : ℝ)*X 0 0+(336979061/625000000 : ℝ)*X 0 1+(658358543/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672218297/5000000000 : ℝ)*X 1 0+(-2194808671/10000000000 : ℝ)*X 1 1+(658358543/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068887319/2000000000 : ℝ)*X 2 0+(658358543/1250000000 : ℝ)*X 2 1+(-68587771/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177106563/5000000000 : ℝ)*X 0 0+(211501317/500000000 : ℝ)*X 0 1+(560245453/1250000000 : ℝ)*X 0 2+(2177106563/5000000000 : ℝ)*X 1 0+(211501317/500000000 : ℝ)*X 1 1+(560245453/1250000000 : ℝ)*X 1 2+(2177106563/5000000000 : ℝ)*X 2 0+(211501317/500000000 : ℝ)*X 2 1+(560245453/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213153243/1000000000 : ℝ)*X 0 0+(329198923/625000000 : ℝ)*X 0 1+(1347837353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312648501/10000000000 : ℝ)*X 1 0+(-414065521/2000000000 : ℝ)*X 1 1+(539134941/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312648501/10000000000 : ℝ)*X 2 0+(1347837353/2500000000 : ℝ)*X 2 1+(-2070327603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177111317/5000000000 : ℝ)*X 0 0+(35850631/80000000 : ℝ)*X 0 1+(2115331697/5000000000 : ℝ)*X 0 2+(2177111317/5000000000 : ℝ)*X 1 0+(35850631/80000000 : ℝ)*X 1 1+(2115331697/5000000000 : ℝ)*X 1 2+(2177111317/5000000000 : ℝ)*X 2 0+(35850631/80000000 : ℝ)*X 2 1+(2115331697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1441382877293856623302760499/331625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33929393/4000000000000 : ℝ)*(base19) + (790600511/100000000000000 : ℝ)*(base23) + (31603603/100000000000000 : ℝ)*(lower2) + (54831343/50000000000000 : ℝ)*(upper3) + (66459089/100000000000000 : ℝ)*(upper5) + (2995587655603707/50000000000000 : ℝ)*(major0) + (2995587655603707/50000000000000 : ℝ)*(major1) + (2995587655603707/50000000000000 : ℝ)*(major2) + (1001632670317627/12500000000000 : ℝ)*(sp0) + (1602616791413989/20000000000000 : ℝ)*(sp1) + (8013084014704259/100000000000000 : ℝ)*(sp2) + (396925311666269/10000000000000 : ℝ)*(sp3) + (11721381877/50000000000000 : ℝ)*(sp4) + (3138891639/25000000000000 : ℝ)*(sp7) + (1984632836114623/50000000000000 : ℝ)*(f.failure) + (801308480530477/10000000000000 : ℝ)*(f.sum) + (1228533397331/6632500000000000000000000000 : ℝ)*base65 + (10352542500434963167/1326500000000000000000000000000000 : ℝ)*base68 + (26740314500516963167/1326500000000000000000000000000000 : ℝ)*base70 + (21777101995363963167/1326500000000000000000000000000000 : ℝ)*base72 + (138611582076383/13265000000000000000000000000 : ℝ)*base74 + (9128894253491036833/1326500000000000000000000000000000 : ℝ)*base75 + (9608309358401463167/1326500000000000000000000000000000 : ℝ)*base78 + (8435259736646963167/1326500000000000000000000000000000 : ℝ)*base80 + (50379551492849/6632500000000000000000000000 : ℝ)*base82 + (361663/19531250000000000000 : ℝ)*base89 + (361663/19531250000000000000 : ℝ)*base91 + (361663/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3788897739357559084858813389/331625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411207507/20000000000000 : ℝ)*(base19) + (1115861481/50000000000000 : ℝ)*(base23) + (229527579/100000000000000 : ℝ)*(upper3) + (4956249/6250000000000 : ℝ)*(lower4) + (23134587/10000000000000 : ℝ)*(upper5) + (1505383858849523/25000000000000 : ℝ)*(major0) + (1505383858849523/25000000000000 : ℝ)*(major1) + (1505383858849523/25000000000000 : ℝ)*(major2) + (14388082587/25000000000000 : ℝ)*(sp1) + (12393532689/20000000000000 : ℝ)*(sp2) + (8053690667747253/100000000000000 : ℝ)*(sp4) + (805363105937937/10000000000000 : ℝ)*(sp5) + (8053626468360847/100000000000000 : ℝ)*(sp6) + (1994689911103669/50000000000000 : ℝ)*(sp7) + (1994689911103669/50000000000000 : ℝ)*(f.failure) + (8053690667747253/100000000000000 : ℝ)*(f.sum) + (11874547259577/6632500000000000000000000000 : ℝ)*base66 + (3632575551546970537/663250000000000000000000000000000 : ℝ)*base67 + (5435733857506470537/663250000000000000000000000000000 : ℝ)*base69 + (2458327029806970537/663250000000000000000000000000000 : ℝ)*base71 + (5749424283751/3316250000000000000000000000 : ℝ)*base74 + (8817506208274470537/663250000000000000000000000000000 : ℝ)*base75 + (1517612007473029463/663250000000000000000000000000000 : ℝ)*base78 + (6192027804258029463/663250000000000000000000000000000 : ℝ)*base80 + (32175777151739/13265000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2583/2441406250000000000 : ℝ)*base89 + (2583/2441406250000000000 : ℝ)*base91 + (2583/2441406250000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_s8_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213152791/1000000000 : ℝ)*x 0 + (2695811991/5000000000 : ℝ)*x 1 + (82295461/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213152791/1000000000 : ℝ)^4205 ≤ (3239880965611/25000000000000 : ℝ)^3181 := by
    have hnat : (213152791 : ℕ)^4205*25000000000000^3181 ≤ 3239880965611^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213152791 1000000000 3239880965611 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695811991/5000000000 : ℝ)^4205 ≤ (8838673380563/20000000000000 : ℝ)^3181 := by
    have hnat : (2695811991 : ℕ)^4205*20000000000000^3181 ≤ 8838673380563^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695811991 5000000000 8838673380563 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82295461/156250000 : ℝ)^4205 ≤ (21423554611257/50000000000000 : ℝ)^3181 := by
    have hnat : (82295461 : ℕ)^4205*50000000000000^3181 ≤ 21423554611257^3181*156250000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82295461 156250000 21423554611257 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213152791/1000000000 : ℝ), (2695811991/5000000000 : ℝ), (82295461/156250000 : ℝ)] ![(3239880965611/25000000000000 : ℝ), (8838673380563/20000000000000 : ℝ), (21423554611257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213152791/1000000000 : ℝ)|^4205 ≤ (3239880965611/25000000000000 : ℝ)^3181
        have hw : |(-213152791/1000000000 : ℝ)|=(213152791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695811991/5000000000 : ℝ)|^4205 ≤ (8838673380563/20000000000000 : ℝ)^3181
        have hw : |(2695811991/5000000000 : ℝ)|=(2695811991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82295461/156250000 : ℝ)|^4205 ≤ (21423554611257/50000000000000 : ℝ)^3181
        have hw : |(82295461/156250000 : ℝ)|=(82295461/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267221363/500000000 : ℝ)*x 0 + (-2194766151/10000000000 : ℝ)*x 1 + (5266909801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267221363/500000000 : ℝ)^4205 ≤ (21841349766273/50000000000000 : ℝ)^3181 := by
    have hnat : (267221363 : ℕ)^4205*50000000000000^3181 ≤ 21841349766273^3181*500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267221363 500000000 21841349766273 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194766151/10000000000 : ℝ)^4205 ≤ (6735094015847/50000000000000 : ℝ)^3181 := by
    have hnat : (2194766151 : ℕ)^4205*50000000000000^3181 ≤ 6735094015847^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194766151 10000000000 6735094015847 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266909801/10000000000 : ℝ)^4205 ≤ (21423556208219/50000000000000 : ℝ)^3181 := by
    have hnat : (5266909801 : ℕ)^4205*50000000000000^3181 ≤ 21423556208219^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266909801 10000000000 21423556208219 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267221363/500000000 : ℝ), (-2194766151/10000000000 : ℝ), (5266909801/10000000000 : ℝ)] ![(21841349766273/50000000000000 : ℝ), (6735094015847/50000000000000 : ℝ), (21423556208219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267221363/500000000 : ℝ)|^4205 ≤ (21841349766273/50000000000000 : ℝ)^3181
        have hw : |(267221363/500000000 : ℝ)|=(267221363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194766151/10000000000 : ℝ)|^4205 ≤ (6735094015847/50000000000000 : ℝ)^3181
        have hw : |(-2194766151/10000000000 : ℝ)|=(2194766151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266909801/10000000000 : ℝ)|^4205 ≤ (21423556208219/50000000000000 : ℝ)^3181
        have hw : |(5266909801/10000000000 : ℝ)|=(5266909801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668053431/1250000000 : ℝ)*x 0 + (5266909577/10000000000 : ℝ)*x 1 + (-1097383099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668053431/1250000000 : ℝ)^4205 ≤ (2184135078191/5000000000000 : ℝ)^3181 := by
    have hnat : (668053431 : ℕ)^4205*5000000000000^3181 ≤ 2184135078191^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668053431 1250000000 2184135078191 5000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266909577/10000000000 : ℝ)^4205 ≤ (42847110007553/100000000000000 : ℝ)^3181 := by
    have hnat : (5266909577 : ℕ)^4205*100000000000000^3181 ≤ 42847110007553^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266909577 10000000000 42847110007553 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097383099/5000000000 : ℝ)^4205 ≤ (13470188413011/100000000000000 : ℝ)^3181 := by
    have hnat : (1097383099 : ℕ)^4205*100000000000000^3181 ≤ 13470188413011^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097383099 5000000000 13470188413011 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668053431/1250000000 : ℝ), (5266909577/10000000000 : ℝ), (-1097383099/5000000000 : ℝ)] ![(2184135078191/5000000000000 : ℝ), (42847110007553/100000000000000 : ℝ), (13470188413011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668053431/1250000000 : ℝ)|^4205 ≤ (2184135078191/5000000000000 : ℝ)^3181
        have hw : |(668053431/1250000000 : ℝ)|=(668053431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266909577/10000000000 : ℝ)|^4205 ≤ (42847110007553/100000000000000 : ℝ)^3181
        have hw : |(5266909577/10000000000 : ℝ)|=(5266909577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097383099/5000000000 : ℝ)|^4205 ≤ (13470188413011/100000000000000 : ℝ)^3181
        have hw : |(-1097383099/5000000000 : ℝ)|=(1097383099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435421549/1000000000 : ℝ)*x 0 + (528763663/1250000000 : ℝ)*x 1 + (4481879849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435421549/1000000000 : ℝ)^4205 ≤ (33317386225163/100000000000000 : ℝ)^3181 := by
    have hnat : (435421549 : ℕ)^4205*100000000000000^3181 ≤ 33317386225163^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435421549 1000000000 33317386225163 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528763663/1250000000 : ℝ)^4205 ≤ (801696401841/2500000000000 : ℝ)^3181 := by
    have hnat : (528763663 : ℕ)^4205*2500000000000^3181 ≤ 801696401841^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528763663 1250000000 801696401841 2500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481879849/10000000000 : ℝ)^4205 ≤ (8653689421681/25000000000000 : ℝ)^3181 := by
    have hnat : (4481879849 : ℕ)^4205*25000000000000^3181 ≤ 8653689421681^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481879849 10000000000 8653689421681 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435421549/1000000000 : ℝ), (528763663/1250000000 : ℝ), (4481879849/10000000000 : ℝ)] ![(33317386225163/100000000000000 : ℝ), (801696401841/2500000000000 : ℝ), (8653689421681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435421549/1000000000 : ℝ)|^4205 ≤ (33317386225163/100000000000000 : ℝ)^3181
        have hw : |(435421549/1000000000 : ℝ)|=(435421549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528763663/1250000000 : ℝ)|^4205 ≤ (801696401841/2500000000000 : ℝ)^3181
        have hw : |(528763663/1250000000 : ℝ)|=(528763663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481879849/10000000000 : ℝ)|^4205 ≤ (8653689421681/25000000000000 : ℝ)^3181
        have hw : |(4481879849/10000000000 : ℝ)|=(4481879849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065766021/5000000000 : ℝ)*x 0 + (5267223853/10000000000 : ℝ)*x 1 + (5391308921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065766021/5000000000 : ℝ)^4205 ≤ (6479778535913/50000000000000 : ℝ)^3181 := by
    have hnat : (1065766021 : ℕ)^4205*50000000000000^3181 ≤ 6479778535913^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065766021 5000000000 6479778535913 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267223853/10000000000 : ℝ)^4205 ≤ (21425244874163/50000000000000 : ℝ)^3181 := by
    have hnat : (5267223853 : ℕ)^4205*50000000000000^3181 ≤ 21425244874163^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267223853 10000000000 21425244874163 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391308921/10000000000 : ℝ)^4205 ≤ (44189953163241/100000000000000 : ℝ)^3181 := by
    have hnat : (5391308921 : ℕ)^4205*100000000000000^3181 ≤ 44189953163241^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391308921 10000000000 44189953163241 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065766021/5000000000 : ℝ), (5267223853/10000000000 : ℝ), (5391308921/10000000000 : ℝ)] ![(6479778535913/50000000000000 : ℝ), (21425244874163/50000000000000 : ℝ), (44189953163241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065766021/5000000000 : ℝ)|^4205 ≤ (6479778535913/50000000000000 : ℝ)^3181
        have hw : |(-1065766021/5000000000 : ℝ)|=(1065766021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267223853/10000000000 : ℝ)|^4205 ≤ (21425244874163/50000000000000 : ℝ)^3181
        have hw : |(5267223853/10000000000 : ℝ)|=(5267223853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391308921/10000000000 : ℝ)|^4205 ≤ (44189953163241/100000000000000 : ℝ)^3181
        have hw : |(5391308921/10000000000 : ℝ)|=(5391308921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656330033/5000000000 : ℝ)*x 0 + (-2070367167/10000000000 : ℝ)*x 1 + (1347827207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656330033/5000000000 : ℝ)^4205 ≤ (2708737187353/6250000000000 : ℝ)^3181 := by
    have hnat : (2656330033 : ℕ)^4205*6250000000000^3181 ≤ 2708737187353^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656330033 5000000000 2708737187353 6250000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070367167/10000000000 : ℝ)^4205 ≤ (3117563208043/25000000000000 : ℝ)^3181 := by
    have hnat : (2070367167 : ℕ)^4205*25000000000000^3181 ≤ 3117563208043^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070367167 10000000000 3117563208043 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347827207/2500000000 : ℝ)^4205 ≤ (44189952155579/100000000000000 : ℝ)^3181 := by
    have hnat : (1347827207 : ℕ)^4205*100000000000000^3181 ≤ 44189952155579^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347827207 2500000000 44189952155579 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656330033/5000000000 : ℝ), (-2070367167/10000000000 : ℝ), (1347827207/2500000000 : ℝ)] ![(2708737187353/6250000000000 : ℝ), (3117563208043/25000000000000 : ℝ), (44189952155579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656330033/5000000000 : ℝ)|^4205 ≤ (2708737187353/6250000000000 : ℝ)^3181
        have hw : |(2656330033/5000000000 : ℝ)|=(2656330033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070367167/10000000000 : ℝ)|^4205 ≤ (3117563208043/25000000000000 : ℝ)^3181
        have hw : |(-2070367167/10000000000 : ℝ)|=(2070367167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347827207/2500000000 : ℝ)|^4205 ≤ (44189952155579/100000000000000 : ℝ)^3181
        have hw : |(1347827207/2500000000 : ℝ)|=(1347827207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312660319/10000000000 : ℝ)*x 0 + (5391308687/10000000000 : ℝ)*x 1 + (-258795877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312660319/10000000000 : ℝ)^4205 ≤ (21669898862991/50000000000000 : ℝ)^3181 := by
    have hnat : (5312660319 : ℕ)^4205*50000000000000^3181 ≤ 21669898862991^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312660319 10000000000 21669898862991 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391308687/10000000000 : ℝ)^4205 ≤ (8837990125567/20000000000000 : ℝ)^3181 := by
    have hnat : (5391308687 : ℕ)^4205*20000000000000^3181 ≤ 8837990125567^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391308687 10000000000 8837990125567 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258795877/1250000000 : ℝ)^4205 ≤ (194847681717/1562500000000 : ℝ)^3181 := by
    have hnat : (258795877 : ℕ)^4205*1562500000000^3181 ≤ 194847681717^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258795877 1250000000 194847681717 1562500000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312660319/10000000000 : ℝ), (5391308687/10000000000 : ℝ), (-258795877/1250000000 : ℝ)] ![(21669898862991/50000000000000 : ℝ), (8837990125567/20000000000000 : ℝ), (194847681717/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312660319/10000000000 : ℝ)|^4205 ≤ (21669898862991/50000000000000 : ℝ)^3181
        have hw : |(5312660319/10000000000 : ℝ)|=(5312660319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391308687/10000000000 : ℝ)|^4205 ≤ (8837990125567/20000000000000 : ℝ)^3181
        have hw : |(5391308687/10000000000 : ℝ)|=(5391308687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258795877/1250000000 : ℝ)|^4205 ≤ (194847681717/1562500000000 : ℝ)^3181
        have hw : |(-258795877/1250000000 : ℝ)|=(258795877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s8_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (27213901/62500000 : ℝ)*x 0 + (4481246239/10000000000 : ℝ)*x 1 + (846149207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27213901/62500000 : ℝ)^4205 ≤ (16658736960863/50000000000000 : ℝ)^3181 := by
    have hnat : (27213901 : ℕ)^4205*50000000000000^3181 ≤ 16658736960863^3181*62500000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27213901 62500000 16658736960863 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481246239/10000000000 : ℝ)^4205 ≤ (8652072252091/25000000000000 : ℝ)^3181 := by
    have hnat : (4481246239 : ℕ)^4205*25000000000000^3181 ≤ 8652072252091^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481246239 10000000000 8652072252091 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846149207/2000000000 : ℝ)^4205 ≤ (16037118525349/50000000000000 : ℝ)^3181 := by
    have hnat : (846149207 : ℕ)^4205*50000000000000^3181 ≤ 16037118525349^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846149207 2000000000 16037118525349 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27213901/62500000 : ℝ), (4481246239/10000000000 : ℝ), (846149207/2000000000 : ℝ)] ![(16658736960863/50000000000000 : ℝ), (8652072252091/25000000000000 : ℝ), (16037118525349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27213901/62500000 : ℝ)|^4205 ≤ (16658736960863/50000000000000 : ℝ)^3181
        have hw : |(27213901/62500000 : ℝ)|=(27213901/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481246239/10000000000 : ℝ)|^4205 ≤ (8652072252091/25000000000000 : ℝ)^3181
        have hw : |(4481246239/10000000000 : ℝ)|=(4481246239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846149207/2000000000 : ℝ)|^4205 ≤ (16037118525349/50000000000000 : ℝ)^3181
        have hw : |(846149207/2000000000 : ℝ)|=(846149207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14091/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1431/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1431/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1431/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1431/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1431/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1431/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1431/12500 : ℝ) ^ (8409/2048 : ℝ) ≤ (13651622422240149/100000000000000000000 : ℝ) := by
    have hpowers : (1431/12500 : ℝ)^8409 ≤ (13651622422240149/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1431 : ℕ)^8409*100000000000000000000^2048 ≤ 13651622422240149^2048*12500^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1431 12500 13651622422240149 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1431/12500 : ℝ)) (X := (13651622422240149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3523/25000 : ℝ) ^ (8409/2048 : ℝ) ≤ (16020947941043389/50000000000000000000 : ℝ) := by
    have hpowers : (3523/25000 : ℝ)^8409 ≤ (16020947941043389/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3523 : ℕ)^8409*50000000000000000000^2048 ≤ 16020947941043389^2048*25000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 25000 16020947941043389 50000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/25000 : ℝ)) (X := (16020947941043389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013651622422240149/50000000000000000000 : ℝ) ≤ (2000132979597881/2000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50013651622422240149/50000000000000000000 : ℝ)^2048 ≤ (2000132979597881/2000000000000000 : ℝ)^8409 := by
      have hnat : (50013651622422240149 : ℕ)^2048*2000000000000000^8409 ≤ 2000132979597881^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013651622422240149 50000000000000000000 2000132979597881 2000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000132979597881/2000000000000000 : ℝ)) (X := (50013651622422240149/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045693518304326927/100000000000000000000 : ℝ) ≤ (400044506674671/400000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100045693518304326927/100000000000000000000 : ℝ)^2048 ≤ (400044506674671/400000000000000 : ℝ)^8409 := by
      have hnat : (100045693518304326927 : ℕ)^2048*400000000000000^8409 ≤ 400044506674671^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045693518304326927 100000000000000000000 400044506674671 400000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400044506674671/400000000000000 : ℝ)) (X := (100045693518304326927/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016020947941043389/25000000000000000000 : ℝ) ≤ (2000312087148829/2000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (25016020947941043389/25000000000000000000 : ℝ)^2048 ≤ (2000312087148829/2000000000000000 : ℝ)^8409 := by
      have hnat : (25016020947941043389 : ℕ)^2048*2000000000000000^8409 ≤ 2000312087148829^8409*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016020947941043389 25000000000000000000 2000312087148829 2000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000312087148829/2000000000000000 : ℝ)) (X := (25016020947941043389/25000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13651622422240149/100000000000000000000 : ℝ) ≤ ((264315058740677233/264400000000000000 : ℝ)+2*(44776887737/26440000000000 : ℝ)*(1431/12500 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (264315058740677233/264400000000000000 : ℝ)+2*(44776887737/26440000000000 : ℝ)*(1431/12500 : ℝ)=(2000132979597881/2000000000000000 : ℝ) by norm_num, show 1+2*(13651622422240149/100000000000000000000 : ℝ)=(50013651622422240149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16020947941043389/50000000000000000000 : ℝ)+(13651622422240149/100000000000000000000 : ℝ) ≤ ((264315058740677233/264400000000000000 : ℝ)+(44776887737/26440000000000 : ℝ)*((3523/25000 : ℝ)+(1431/12500 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (264315058740677233/264400000000000000 : ℝ)+(44776887737/26440000000000 : ℝ)*((3523/25000 : ℝ)+(1431/12500 : ℝ))=(400044506674671/400000000000000 : ℝ) by norm_num, show 1+(16020947941043389/50000000000000000000 : ℝ)+(13651622422240149/100000000000000000000 : ℝ)=(100045693518304326927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16020947941043389/50000000000000000000 : ℝ) ≤ ((264315058740677233/264400000000000000 : ℝ)+2*(44776887737/26440000000000 : ℝ)*(3523/25000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (264315058740677233/264400000000000000 : ℝ)+2*(44776887737/26440000000000 : ℝ)*(3523/25000 : ℝ)=(2000312087148829/2000000000000000 : ℝ) by norm_num, show 1+2*(16020947941043389/50000000000000000000 : ℝ)=(25016020947941043389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (264315058740677233/264400000000000000 : ℝ)*(X 1 0+X 2 0)+(44776887737/26440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (264315058740677233/264400000000000000 : ℝ)) (alpha := (44776887737/26440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (264315058740677233/264400000000000000 : ℝ)*(X 0 1+X 2 1)+(44776887737/26440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (264315058740677233/264400000000000000 : ℝ)) (alpha := (44776887737/26440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (264315058740677233/264400000000000000 : ℝ)*(X 0 2+X 1 2)+(44776887737/26440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (264315058740677233/264400000000000000 : ℝ)) (alpha := (44776887737/26440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213152791/1000000000 : ℝ)*X 0 0+(2695811991/5000000000 : ℝ)*X 0 1+(82295461/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267221363/500000000 : ℝ)*X 1 0+(-2194766151/10000000000 : ℝ)*X 1 1+(5266909801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668053431/1250000000 : ℝ)*X 2 0+(5266909577/10000000000 : ℝ)*X 2 1+(-1097383099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435421549/1000000000 : ℝ)*X 0 0+(528763663/1250000000 : ℝ)*X 0 1+(4481879849/10000000000 : ℝ)*X 0 2+(435421549/1000000000 : ℝ)*X 1 0+(528763663/1250000000 : ℝ)*X 1 1+(4481879849/10000000000 : ℝ)*X 1 2+(435421549/1000000000 : ℝ)*X 2 0+(528763663/1250000000 : ℝ)*X 2 1+(4481879849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065766021/5000000000 : ℝ)*X 0 0+(5267223853/10000000000 : ℝ)*X 0 1+(5391308921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656330033/5000000000 : ℝ)*X 1 0+(-2070367167/10000000000 : ℝ)*X 1 1+(1347827207/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312660319/10000000000 : ℝ)*X 2 0+(5391308687/10000000000 : ℝ)*X 2 1+(-258795877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((27213901/62500000 : ℝ)*X 0 0+(4481246239/10000000000 : ℝ)*X 0 1+(846149207/2000000000 : ℝ)*X 0 2+(27213901/62500000 : ℝ)*X 1 0+(4481246239/10000000000 : ℝ)*X 1 1+(846149207/2000000000 : ℝ)*X 1 2+(27213901/62500000 : ℝ)*X 2 0+(4481246239/10000000000 : ℝ)*X 2 1+(846149207/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10095257144466520244632053/13220000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1133888827/100000000000000 : ℝ)*(base19) + (1306446279/100000000000000 : ℝ)*(base23) + (8543119/4000000000000 : ℝ)*(upper3) + (58523929/100000000000000 : ℝ)*(upper4) + (10938949/10000000000000 : ℝ)*(upper5) + (5995153553885949/100000000000000 : ℝ)*(major0) + (5995153553885949/100000000000000 : ℝ)*(major1) + (5995153553885949/100000000000000 : ℝ)*(major2) + (8018360633275601/100000000000000 : ℝ)*(sp0) + (1603680923207181/20000000000000 : ℝ)*(sp1) + (2004601110869613/25000000000000 : ℝ)*(sp2) + (248242737390767/6250000000000 : ℝ)*(sp3) + (4511664913/10000000000000 : ℝ)*(sp4) + (2191767547/12500000000000 : ℝ)*(sp7) + (3971901332392647/100000000000000 : ℝ)*(f.failure) + (2004601437481183/25000000000000 : ℝ)*(f.sum) + (2916142645127/1322000000000000000000000000 : ℝ)*base66 + (210943860121530883/26440000000000000000000000000000 : ℝ)*base68 + (341843834352650883/26440000000000000000000000000000 : ℝ)*base70 + (543093772068570883/26440000000000000000000000000000 : ℝ)*base72 + (4924132182421/1322000000000000000000000000 : ℝ)*base74 + (554905399277890883/26440000000000000000000000000000 : ℝ)*base76 + (269296472450810883/26440000000000000000000000000000 : ℝ)*base78 + (250529133595610883/26440000000000000000000000000000 : ℝ)*base80 + (6933542695211/1322000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (198957/39062500000000000000 : ℝ)*base89 + (198957/39062500000000000000 : ℝ)*base91 + (198957/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154456352012918394488251623/13220000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1095036319/100000000000000 : ℝ)*(base19) + (93837133/5000000000000 : ℝ)*(base23) + (284245197/50000000000000 : ℝ)*(lower1) + (8710971/25000000000000 : ℝ)*(lower3) + (74919751/50000000000000 : ℝ)*(lower4) + (6025475708270723/100000000000000 : ℝ)*(major0) + (6025475708270723/100000000000000 : ℝ)*(major1) + (6025475708270723/100000000000000 : ℝ)*(major2) + (1670850619/20000000000000 : ℝ)*(sp0) + (775176707/4000000000000 : ℝ)*(sp2) + (1007369043271599/12500000000000 : ℝ)*(sp4) + (8058959605389569/100000000000000 : ℝ)*(sp5) + (8058939444265553/100000000000000 : ℝ)*(sp6) + (1995995163332167/50000000000000 : ℝ)*(sp7) + (1995995163332167/50000000000000 : ℝ)*(f.failure) + (251842521888309/3125000000000 : ℝ)*(f.sum) + (7409792707921/1322000000000000000000000000 : ℝ)*base66 + (266878029028579459/26440000000000000000000000000000 : ℝ)*base67 + (325253944992179459/26440000000000000000000000000000 : ℝ)*base69 + (35217196116300541/26440000000000000000000000000000 : ℝ)*base72 + (11655017257/264400000000000000000000000 : ℝ)*base73 + (559649229631379459/26440000000000000000000000000000 : ℝ)*base75 + (99963025325620541/26440000000000000000000000000000 : ℝ)*base78 + (388962071279779459/26440000000000000000000000000000 : ℝ)*base79 + (4942526518027/1322000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (140529/39062500000000000000 : ℝ)*base89 + (140529/39062500000000000000 : ℝ)*base91 + (140529/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1217_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1217_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1217_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1217_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

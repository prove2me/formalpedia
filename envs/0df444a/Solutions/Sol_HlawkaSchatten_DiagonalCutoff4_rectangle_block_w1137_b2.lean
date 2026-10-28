-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1137_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:59.566166+00:00
-- url     : https://prove2.me/submissions/7553d1e7-f75f-4995-81be-436eb249fa22

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
theorem support_rectangle_w1137_s6_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216924689/1000000000 : ℝ)*x 0 + (5393482801/10000000000 : ℝ)*x 1 + (5265321161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216924689/1000000000 : ℝ)^4165 ≤ (13180701595357/100000000000000 : ℝ)^3141 := by
    have hnat : (216924689 : ℕ)^4165*100000000000000^3141 ≤ 13180701595357^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216924689 1000000000 13180701595357 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393482801/10000000000 : ℝ)^4165 ≤ (44101746338161/100000000000000 : ℝ)^3141 := by
    have hnat : (5393482801 : ℕ)^4165*100000000000000^3141 ≤ 44101746338161^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393482801 10000000000 44101746338161 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265321161/10000000000 : ℝ)^4165 ≤ (42717552053913/100000000000000 : ℝ)^3141 := by
    have hnat : (5265321161 : ℕ)^4165*100000000000000^3141 ≤ 42717552053913^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265321161 10000000000 42717552053913 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216924689/1000000000 : ℝ), (5393482801/10000000000 : ℝ), (5265321161/10000000000 : ℝ)] ![(13180701595357/100000000000000 : ℝ), (44101746338161/100000000000000 : ℝ), (42717552053913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216924689/1000000000 : ℝ)|^4165 ≤ (13180701595357/100000000000000 : ℝ)^3141
        have hw : |(-216924689/1000000000 : ℝ)|=(216924689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393482801/10000000000 : ℝ)|^4165 ≤ (44101746338161/100000000000000 : ℝ)^3141
        have hw : |(5393482801/10000000000 : ℝ)|=(5393482801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265321161/10000000000 : ℝ)|^4165 ≤ (42717552053913/100000000000000 : ℝ)^3141
        have hw : |(5265321161/10000000000 : ℝ)|=(5265321161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344866751/10000000000 : ℝ)*x 0 + (-446851801/2000000000 : ℝ)*x 1 + (2632660581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344866751/10000000000 : ℝ)^4165 ≤ (43575397888401/100000000000000 : ℝ)^3141 := by
    have hnat : (5344866751 : ℕ)^4165*100000000000000^3141 ≤ 43575397888401^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344866751 10000000000 43575397888401 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446851801/2000000000 : ℝ)^4165 ≤ (1370705003807/10000000000000 : ℝ)^3141 := by
    have hnat : (446851801 : ℕ)^4165*10000000000000^3141 ≤ 1370705003807^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446851801 2000000000 1370705003807 10000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632660581/5000000000 : ℝ)^4165 ≤ (42717552064671/100000000000000 : ℝ)^3141 := by
    have hnat : (2632660581 : ℕ)^4165*100000000000000^3141 ≤ 42717552064671^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632660581 5000000000 42717552064671 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344866751/10000000000 : ℝ), (-446851801/2000000000 : ℝ), (2632660581/5000000000 : ℝ)] ![(43575397888401/100000000000000 : ℝ), (1370705003807/10000000000000 : ℝ), (42717552064671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344866751/10000000000 : ℝ)|^4165 ≤ (43575397888401/100000000000000 : ℝ)^3141
        have hw : |(5344866751/10000000000 : ℝ)|=(5344866751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446851801/2000000000 : ℝ)|^4165 ≤ (1370705003807/10000000000000 : ℝ)^3141
        have hw : |(-446851801/2000000000 : ℝ)|=(446851801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632660581/5000000000 : ℝ)|^4165 ≤ (42717552064671/100000000000000 : ℝ)^3141
        have hw : |(2632660581/5000000000 : ℝ)|=(2632660581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344866747/10000000000 : ℝ)*x 0 + (5265321163/10000000000 : ℝ)*x 1 + (-34910297/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344866747/10000000000 : ℝ)^4165 ≤ (43575397845159/100000000000000 : ℝ)^3141 := by
    have hnat : (5344866747 : ℕ)^4165*100000000000000^3141 ≤ 43575397845159^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344866747 10000000000 43575397845159 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265321163/10000000000 : ℝ)^4165 ≤ (42717552075429/100000000000000 : ℝ)^3141 := by
    have hnat : (5265321163 : ℕ)^4165*100000000000000^3141 ≤ 42717552075429^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265321163 10000000000 42717552075429 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34910297/156250000 : ℝ)^4165 ≤ (548282002499/4000000000000 : ℝ)^3141 := by
    have hnat : (34910297 : ℕ)^4165*4000000000000^3141 ≤ 548282002499^3141*156250000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34910297 156250000 548282002499 4000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344866747/10000000000 : ℝ), (5265321163/10000000000 : ℝ), (-34910297/156250000 : ℝ)] ![(43575397845159/100000000000000 : ℝ), (42717552075429/100000000000000 : ℝ), (548282002499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344866747/10000000000 : ℝ)|^4165 ≤ (43575397845159/100000000000000 : ℝ)^3141
        have hw : |(5344866747/10000000000 : ℝ)|=(5344866747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265321163/10000000000 : ℝ)|^4165 ≤ (42717552075429/100000000000000 : ℝ)^3141
        have hw : |(5265321163/10000000000 : ℝ)|=(5265321163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34910297/156250000 : ℝ)|^4165 ≤ (548282002499/4000000000000 : ℝ)^3141
        have hw : |(-34910297/156250000 : ℝ)|=(34910297/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873072049/2000000000 : ℝ)*x 0 + (264990569/625000000 : ℝ)*x 1 + (2247286667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873072049/2000000000 : ℝ)^4165 ≤ (33316758547891/100000000000000 : ℝ)^3141 := by
    have hnat : (873072049 : ℕ)^4165*100000000000000^3141 ≤ 33316758547891^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873072049 2000000000 33316758547891 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264990569/625000000 : ℝ)^4165 ≤ (8013137698511/25000000000000 : ℝ)^3141 := by
    have hnat : (264990569 : ℕ)^4165*25000000000000^3141 ≤ 8013137698511^3141*625000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264990569 625000000 8013137698511 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247286667/5000000000 : ℝ)^4165 ≤ (4328836330373/12500000000000 : ℝ)^3141 := by
    have hnat : (2247286667 : ℕ)^4165*12500000000000^3141 ≤ 4328836330373^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247286667 5000000000 4328836330373 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873072049/2000000000 : ℝ), (264990569/625000000 : ℝ), (2247286667/5000000000 : ℝ)] ![(33316758547891/100000000000000 : ℝ), (8013137698511/25000000000000 : ℝ), (4328836330373/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873072049/2000000000 : ℝ)|^4165 ≤ (33316758547891/100000000000000 : ℝ)^3141
        have hw : |(873072049/2000000000 : ℝ)|=(873072049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264990569/625000000 : ℝ)|^4165 ≤ (8013137698511/25000000000000 : ℝ)^3141
        have hw : |(264990569/625000000 : ℝ)|=(264990569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247286667/5000000000 : ℝ)|^4165 ≤ (4328836330373/12500000000000 : ℝ)^3141
        have hw : |(2247286667/5000000000 : ℝ)|=(2247286667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-271156493/1250000000 : ℝ)*x 0 + (5265644719/10000000000 : ℝ)*x 1 + (674144751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271156493/1250000000 : ℝ)^4165 ≤ (2636148463151/20000000000000 : ℝ)^3141 := by
    have hnat : (271156493 : ℕ)^4165*20000000000000^3141 ≤ 2636148463151^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271156493 1250000000 2636148463151 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265644719/10000000000 : ℝ)^4165 ≤ (21360516450931/50000000000000 : ℝ)^3141 := by
    have hnat : (5265644719 : ℕ)^4165*50000000000000^3141 ≤ 21360516450931^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265644719 10000000000 21360516450931 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674144751/1250000000 : ℝ)^4165 ≤ (1102455619279/2500000000000 : ℝ)^3141 := by
    have hnat : (674144751 : ℕ)^4165*2500000000000^3141 ≤ 1102455619279^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674144751 1250000000 1102455619279 2500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271156493/1250000000 : ℝ), (5265644719/10000000000 : ℝ), (674144751/1250000000 : ℝ)] ![(2636148463151/20000000000000 : ℝ), (21360516450931/50000000000000 : ℝ), (1102455619279/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271156493/1250000000 : ℝ)|^4165 ≤ (2636148463151/20000000000000 : ℝ)^3141
        have hw : |(-271156493/1250000000 : ℝ)|=(271156493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265644719/10000000000 : ℝ)|^4165 ≤ (21360516450931/50000000000000 : ℝ)^3141
        have hw : |(5265644719/10000000000 : ℝ)|=(5265644719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674144751/1250000000 : ℝ)|^4165 ≤ (1102455619279/2500000000000 : ℝ)^3141
        have hw : |(674144751/1250000000 : ℝ)|=(674144751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328102129/2500000000 : ℝ)*x 0 + (-2106422227/10000000000 : ℝ)*x 1 + (5393157921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328102129/2500000000 : ℝ)^4165 ≤ (43224851303903/100000000000000 : ℝ)^3141 := by
    have hnat : (1328102129 : ℕ)^4165*100000000000000^3141 ≤ 43224851303903^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328102129 2500000000 43224851303903 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106422227/10000000000 : ℝ)^4165 ≤ (507076994539/4000000000000 : ℝ)^3141 := by
    have hnat : (2106422227 : ℕ)^4165*4000000000000^3141 ≤ 507076994539^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106422227 10000000000 507076994539 4000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393157921/10000000000 : ℝ)^4165 ≤ (1378069494621/3125000000000 : ℝ)^3141 := by
    have hnat : (5393157921 : ℕ)^4165*3125000000000^3141 ≤ 1378069494621^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393157921 10000000000 1378069494621 3125000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328102129/2500000000 : ℝ), (-2106422227/10000000000 : ℝ), (5393157921/10000000000 : ℝ)] ![(43224851303903/100000000000000 : ℝ), (507076994539/4000000000000 : ℝ), (1378069494621/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328102129/2500000000 : ℝ)|^4165 ≤ (43224851303903/100000000000000 : ℝ)^3141
        have hw : |(1328102129/2500000000 : ℝ)|=(1328102129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106422227/10000000000 : ℝ)|^4165 ≤ (507076994539/4000000000000 : ℝ)^3141
        have hw : |(-2106422227/10000000000 : ℝ)|=(2106422227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393157921/10000000000 : ℝ)|^4165 ≤ (1378069494621/3125000000000 : ℝ)^3141
        have hw : |(5393157921/10000000000 : ℝ)|=(5393157921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312408619/10000000000 : ℝ)*x 0 + (5393157743/10000000000 : ℝ)*x 1 + (-2106422329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312408619/10000000000 : ℝ)^4165 ≤ (4322485241519/10000000000000 : ℝ)^3141 := by
    have hnat : (5312408619 : ℕ)^4165*10000000000000^3141 ≤ 4322485241519^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312408619 10000000000 4322485241519 10000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393157743/10000000000 : ℝ)^4165 ≤ (44098221897927/100000000000000 : ℝ)^3141 := by
    have hnat : (5393157743 : ℕ)^4165*100000000000000^3141 ≤ 44098221897927^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393157743 10000000000 44098221897927 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106422329/10000000000 : ℝ)^4165 ≤ (12676925677459/100000000000000 : ℝ)^3141 := by
    have hnat : (2106422329 : ℕ)^4165*100000000000000^3141 ≤ 12676925677459^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106422329 10000000000 12676925677459 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312408619/10000000000 : ℝ), (5393157743/10000000000 : ℝ), (-2106422329/10000000000 : ℝ)] ![(4322485241519/10000000000000 : ℝ), (44098221897927/100000000000000 : ℝ), (12676925677459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312408619/10000000000 : ℝ)|^4165 ≤ (4322485241519/10000000000000 : ℝ)^3141
        have hw : |(5312408619/10000000000 : ℝ)|=(5312408619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393157743/10000000000 : ℝ)|^4165 ≤ (44098221897927/100000000000000 : ℝ)^3141
        have hw : |(5393157743/10000000000 : ℝ)|=(5393157743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106422329/10000000000 : ℝ)|^4165 ≤ (12676925677459/100000000000000 : ℝ)^3141
        have hw : |(-2106422329/10000000000 : ℝ)|=(2106422329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s6_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365370007/10000000000 : ℝ)*x 0 + (4493930123/10000000000 : ℝ)*x 1 + (212024739/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365370007/10000000000 : ℝ)^4165 ≤ (16658428670731/50000000000000 : ℝ)^3141 := by
    have hnat : (4365370007 : ℕ)^4165*50000000000000^3141 ≤ 16658428670731^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365370007 10000000000 16658428670731 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493930123/10000000000 : ℝ)^4165 ≤ (8656029791153/25000000000000 : ℝ)^3141 := by
    have hnat : (4493930123 : ℕ)^4165*25000000000000^3141 ≤ 8656029791153^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493930123 10000000000 8656029791153 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212024739/500000000 : ℝ)^4165 ≤ (16029511741147/50000000000000 : ℝ)^3141 := by
    have hnat : (212024739 : ℕ)^4165*50000000000000^3141 ≤ 16029511741147^3141*500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212024739 500000000 16029511741147 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365370007/10000000000 : ℝ), (4493930123/10000000000 : ℝ), (212024739/500000000 : ℝ)] ![(16658428670731/50000000000000 : ℝ), (8656029791153/25000000000000 : ℝ), (16029511741147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365370007/10000000000 : ℝ)|^4165 ≤ (16658428670731/50000000000000 : ℝ)^3141
        have hw : |(4365370007/10000000000 : ℝ)|=(4365370007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493930123/10000000000 : ℝ)|^4165 ≤ (8656029791153/25000000000000 : ℝ)^3141
        have hw : |(4493930123/10000000000 : ℝ)|=(4493930123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212024739/500000000 : ℝ)|^4165 ≤ (16029511741147/50000000000000 : ℝ)^3141
        have hw : |(212024739/500000000 : ℝ)|=(212024739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2827/25000 : ℝ) ^ (8329/2048 : ℝ) ≤ (2826505804993311/20000000000000000000 : ℝ) := by
    have hpowers : (2827/25000 : ℝ)^8329 ≤ (2826505804993311/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2827 : ℕ)^8329*20000000000000000000^2048 ≤ 2826505804993311^2048*25000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 25000 2826505804993311 20000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/25000 : ℝ)) (X := (2826505804993311/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (8329/2048 : ℝ) ≤ (4317622665854571/12500000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^8329 ≤ (4317622665854571/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14087 : ℕ)^8329*12500000000000000000^2048 ≤ 4317622665854571^2048*100000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 4317622665854571 12500000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (4317622665854571/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002826505804993311/10000000000000000000 : ℝ) ≤ (5000347464705301/5000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (10002826505804993311/10000000000000000000 : ℝ)^2048 ≤ (5000347464705301/5000000000000000 : ℝ)^8329 := by
      have hnat : (10002826505804993311 : ℕ)^2048*5000000000000000^8329 ≤ 5000347464705301^8329*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002826505804993311 10000000000000000000 5000347464705301 5000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000347464705301/5000000000000000 : ℝ)) (X := (10002826505804993311/10000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048673510351803123/100000000000000000000 : ℝ) ≤ (2000239320590411/2000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (100048673510351803123/100000000000000000000 : ℝ)^2048 ≤ (2000239320590411/2000000000000000 : ℝ)^8329 := by
      have hnat : (100048673510351803123 : ℕ)^2048*2000000000000000^8329 ≤ 2000239320590411^8329*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048673510351803123 100000000000000000000 2000239320590411 2000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000239320590411/2000000000000000 : ℝ)) (X := (100048673510351803123/100000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254317622665854571/6250000000000000000 : ℝ) ≤ (2500424569123377/2500000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (6254317622665854571/6250000000000000000 : ℝ)^2048 ≤ (2500424569123377/2500000000000000 : ℝ)^8329 := by
      have hnat : (6254317622665854571 : ℕ)^2048*2500000000000000^8329 ≤ 2500424569123377^8329*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254317622665854571 6250000000000000000 2500424569123377 2500000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500424569123377/2500000000000000 : ℝ)) (X := (6254317622665854571/6250000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2826505804993311/20000000000000000000 : ℝ) ≤ ((396865505143122313/397000000000000000 : ℝ)+2*(71667648779/39700000000000 : ℝ)*(2827/25000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (396865505143122313/397000000000000000 : ℝ)+2*(71667648779/39700000000000 : ℝ)*(2827/25000 : ℝ)=(5000347464705301/5000000000000000 : ℝ) by norm_num, show 1+2*(2826505804993311/20000000000000000000 : ℝ)=(10002826505804993311/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4317622665854571/12500000000000000000 : ℝ)+(2826505804993311/20000000000000000000 : ℝ) ≤ ((396865505143122313/397000000000000000 : ℝ)+(71667648779/39700000000000 : ℝ)*((14087/100000 : ℝ)+(2827/25000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (396865505143122313/397000000000000000 : ℝ)+(71667648779/39700000000000 : ℝ)*((14087/100000 : ℝ)+(2827/25000 : ℝ))=(2000239320590411/2000000000000000 : ℝ) by norm_num, show 1+(4317622665854571/12500000000000000000 : ℝ)+(2826505804993311/20000000000000000000 : ℝ)=(100048673510351803123/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4317622665854571/12500000000000000000 : ℝ) ≤ ((396865505143122313/397000000000000000 : ℝ)+2*(71667648779/39700000000000 : ℝ)*(14087/100000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (396865505143122313/397000000000000000 : ℝ)+2*(71667648779/39700000000000 : ℝ)*(14087/100000 : ℝ)=(2500424569123377/2500000000000000 : ℝ) by norm_num, show 1+2*(4317622665854571/12500000000000000000 : ℝ)=(6254317622665854571/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (396865505143122313/397000000000000000 : ℝ)*(X 1 0+X 2 0)+(71667648779/39700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (396865505143122313/397000000000000000 : ℝ)) (alpha := (71667648779/39700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (396865505143122313/397000000000000000 : ℝ)*(X 0 1+X 2 1)+(71667648779/39700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (396865505143122313/397000000000000000 : ℝ)) (alpha := (71667648779/39700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (396865505143122313/397000000000000000 : ℝ)*(X 0 2+X 1 2)+(71667648779/39700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (396865505143122313/397000000000000000 : ℝ)) (alpha := (71667648779/39700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216924689/1000000000 : ℝ)*X 0 0+(5393482801/10000000000 : ℝ)*X 0 1+(5265321161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344866751/10000000000 : ℝ)*X 1 0+(-446851801/2000000000 : ℝ)*X 1 1+(2632660581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344866747/10000000000 : ℝ)*X 2 0+(5265321163/10000000000 : ℝ)*X 2 1+(-34910297/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873072049/2000000000 : ℝ)*X 0 0+(264990569/625000000 : ℝ)*X 0 1+(2247286667/5000000000 : ℝ)*X 0 2+(873072049/2000000000 : ℝ)*X 1 0+(264990569/625000000 : ℝ)*X 1 1+(2247286667/5000000000 : ℝ)*X 1 2+(873072049/2000000000 : ℝ)*X 2 0+(264990569/625000000 : ℝ)*X 2 1+(2247286667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-271156493/1250000000 : ℝ)*X 0 0+(5265644719/10000000000 : ℝ)*X 0 1+(674144751/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328102129/2500000000 : ℝ)*X 1 0+(-2106422227/10000000000 : ℝ)*X 1 1+(5393157921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312408619/10000000000 : ℝ)*X 2 0+(5393157743/10000000000 : ℝ)*X 2 1+(-2106422329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365370007/10000000000 : ℝ)*X 0 0+(4493930123/10000000000 : ℝ)*X 0 1+(212024739/500000000 : ℝ)*X 0 2+(4365370007/10000000000 : ℝ)*X 1 0+(4493930123/10000000000 : ℝ)*X 1 1+(212024739/500000000 : ℝ)*X 1 2+(4365370007/10000000000 : ℝ)*X 2 0+(4493930123/10000000000 : ℝ)*X 2 1+(212024739/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4420220616478128699171/496250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1757212327/100000000000000 : ℝ)*(base19) + (1629099177/100000000000000 : ℝ)*(base23) + (16338419/25000000000000 : ℝ)*(lower2) + (228028453/100000000000000 : ℝ)*(upper3) + (32723357/25000000000000 : ℝ)*(upper5) + (5864303754447053/100000000000000 : ℝ)*(major0) + (5864303754447053/100000000000000 : ℝ)*(major1) + (5864303754447053/100000000000000 : ℝ)*(major2) + (3901348346613817/50000000000000 : ℝ)*(sp0) + (780274224126721/10000000000000 : ℝ)*(sp1) + (195068559234509/2500000000000 : ℝ)*(sp2) + (981459335993859/25000000000000 : ℝ)*(sp3) + (47305251903/100000000000000 : ℝ)*(sp4) + (3233691367/12500000000000 : ℝ)*(sp7) + (3925863213506373/100000000000000 : ℝ)*(f.failure) + (487671499904971/6250000000000 : ℝ)*(f.sum) + (23093338798487/1985000000000000000000000000 : ℝ)*base65 + (689593335006836411/39700000000000000000000000000000 : ℝ)*base68 + (356697815835136411/39700000000000000000000000000000 : ℝ)*base70 + (16791302111136411/39700000000000000000000000000000 : ℝ)*base72 + (10975513780617/1985000000000000000000000000 : ℝ)*base73 + (330197709001463589/39700000000000000000000000000000 : ℝ)*base75 + (526171535751863589/39700000000000000000000000000000 : ℝ)*base77 + (42832537109863589/39700000000000000000000000000000 : ℝ)*base79 + (746281227353/1985000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (47774053/10000000000000000000000 : ℝ)*base89 + (47774053/10000000000000000000000 : ℝ)*base91 + (47774053/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15078525740809941073269099/2481250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1275238131/100000000000000 : ℝ)*(base19) + (47365747/3125000000000 : ℝ)*(base23) + (66750621/100000000000000 : ℝ)*(upper2) + (76954547/100000000000000 : ℝ)*(upper3) + (89842347/50000000000000 : ℝ)*(upper5) + (736756357296603/12500000000000 : ℝ)*(major0) + (736756357296603/12500000000000 : ℝ)*(major1) + (736756357296603/12500000000000 : ℝ)*(major2) + (17299378753/50000000000000 : ℝ)*(sp1) + (1425223273/5000000000000 : ℝ)*(sp2) + (3921162038128429/50000000000000 : ℝ)*(sp4) + (7842288202261221/100000000000000 : ℝ)*(sp5) + (7842294056087493/100000000000000 : ℝ)*(sp6) + (986444359480631/25000000000000 : ℝ)*(sp7) + (986444359480631/25000000000000 : ℝ)*(f.failure) + (3921162038128429/50000000000000 : ℝ)*(f.sum) + (692287116091/496250000000000000000000000 : ℝ)*base66 + (79415883831547739/4962500000000000000000000000000 : ℝ)*base67 + (7862488440172739/4962500000000000000000000000000 : ℝ)*base69 + (26366980377397739/4962500000000000000000000000000 : ℝ)*base71 + (343248281779/1985000000000000000000000000 : ℝ)*base74 + (42561257869510239/4962500000000000000000000000000 : ℝ)*base75 + (52334156142835239/4962500000000000000000000000000 : ℝ)*base77 + (138550495898185239/4962500000000000000000000000000 : ℝ)*base79 + (10717533356459/1985000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12637591/2500000000000000000000 : ℝ)*base89 + (12637591/2500000000000000000000 : ℝ)*base91 + (12637591/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1137_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1137_s7_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-108463869/500000000 : ℝ)*x 0 + (1348288489/2500000000 : ℝ)*x 1 + (5265629753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108463869/500000000 : ℝ)^4165 ≤ (1647618406961/12500000000000 : ℝ)^3141 := by
    have hnat : (108463869 : ℕ)^4165*12500000000000^3141 ≤ 1647618406961^3141*500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108463869 500000000 1647618406961 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348288489/2500000000 : ℝ)^4165 ≤ (44098180837801/100000000000000 : ℝ)^3141 := by
    have hnat : (1348288489 : ℕ)^4165*100000000000000^3141 ≤ 44098180837801^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348288489 2500000000 44098180837801 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265629753/10000000000 : ℝ)^4165 ≤ (10680217973897/25000000000000 : ℝ)^3141 := by
    have hnat : (5265629753 : ℕ)^4165*25000000000000^3141 ≤ 10680217973897^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265629753 10000000000 10680217973897 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108463869/500000000 : ℝ), (1348288489/2500000000 : ℝ), (5265629753/10000000000 : ℝ)] ![(1647618406961/12500000000000 : ℝ), (44098180837801/100000000000000 : ℝ), (10680217973897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108463869/500000000 : ℝ)|^4165 ≤ (1647618406961/12500000000000 : ℝ)^3141
        have hw : |(-108463869/500000000 : ℝ)|=(108463869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348288489/2500000000 : ℝ)|^4165 ≤ (44098180837801/100000000000000 : ℝ)^3141
        have hw : |(1348288489/2500000000 : ℝ)|=(1348288489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265629753/10000000000 : ℝ)|^4165 ≤ (10680217973897/25000000000000 : ℝ)^3141
        have hw : |(5265629753/10000000000 : ℝ)|=(5265629753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672391801/5000000000 : ℝ)*x 0 + (-1116980513/5000000000 : ℝ)*x 1 + (2632815019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672391801/5000000000 : ℝ)^4165 ≤ (34042577341/78125000000 : ℝ)^3141 := by
    have hnat : (2672391801 : ℕ)^4165*78125000000^3141 ≤ 34042577341^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672391801 5000000000 34042577341 78125000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116980513/5000000000 : ℝ)^4165 ≤ (6852313015821/50000000000000 : ℝ)^3141 := by
    have hnat : (1116980513 : ℕ)^4165*50000000000000^3141 ≤ 6852313015821^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116980513 5000000000 6852313015821 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632815019/5000000000 : ℝ)^4165 ≤ (8544174992331/20000000000000 : ℝ)^3141 := by
    have hnat : (2632815019 : ℕ)^4165*20000000000000^3141 ≤ 8544174992331^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632815019 5000000000 8544174992331 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672391801/5000000000 : ℝ), (-1116980513/5000000000 : ℝ), (2632815019/5000000000 : ℝ)] ![(34042577341/78125000000 : ℝ), (6852313015821/50000000000000 : ℝ), (8544174992331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672391801/5000000000 : ℝ)|^4165 ≤ (34042577341/78125000000 : ℝ)^3141
        have hw : |(2672391801/5000000000 : ℝ)|=(2672391801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116980513/5000000000 : ℝ)|^4165 ≤ (6852313015821/50000000000000 : ℝ)^3141
        have hw : |(-1116980513/5000000000 : ℝ)|=(1116980513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632815019/5000000000 : ℝ)|^4165 ≤ (8544174992331/20000000000000 : ℝ)^3141
        have hw : |(2632815019/5000000000 : ℝ)|=(2632815019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672391883/5000000000 : ℝ)*x 0 + (5265629827/10000000000 : ℝ)*x 1 + (-446792217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672391883/5000000000 : ℝ)^4165 ≤ (43574500769417/100000000000000 : ℝ)^3141 := by
    have hnat : (2672391883 : ℕ)^4165*100000000000000^3141 ≤ 43574500769417^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672391883 5000000000 43574500769417 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265629827/10000000000 : ℝ)^4165 ≤ (42720872691689/100000000000000 : ℝ)^3141 := by
    have hnat : (5265629827 : ℕ)^4165*100000000000000^3141 ≤ 42720872691689^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265629827 10000000000 42720872691689 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446792217/2000000000 : ℝ)^4165 ≤ (13704626511587/100000000000000 : ℝ)^3141 := by
    have hnat : (446792217 : ℕ)^4165*100000000000000^3141 ≤ 13704626511587^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446792217 2000000000 13704626511587 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672391883/5000000000 : ℝ), (5265629827/10000000000 : ℝ), (-446792217/2000000000 : ℝ)] ![(43574500769417/100000000000000 : ℝ), (42720872691689/100000000000000 : ℝ), (13704626511587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672391883/5000000000 : ℝ)|^4165 ≤ (43574500769417/100000000000000 : ℝ)^3141
        have hw : |(2672391883/5000000000 : ℝ)|=(2672391883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265629827/10000000000 : ℝ)|^4165 ≤ (42720872691689/100000000000000 : ℝ)^3141
        have hw : |(5265629827/10000000000 : ℝ)|=(5265629827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446792217/2000000000 : ℝ)|^4165 ≤ (13704626511587/100000000000000 : ℝ)^3141
        have hw : |(-446792217/2000000000 : ℝ)|=(446792217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873075361/2000000000 : ℝ)*x 0 + (2120240089/5000000000 : ℝ)*x 1 + (4493937717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873075361/2000000000 : ℝ)^4165 ≤ (33316926138749/100000000000000 : ℝ)^3141 := by
    have hnat : (873075361 : ℕ)^4165*100000000000000^3141 ≤ 33316926138749^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873075361 2000000000 33316926138749 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120240089/5000000000 : ℝ)^4165 ≤ (8014719274631/25000000000000 : ℝ)^3141 := by
    have hnat : (2120240089 : ℕ)^4165*25000000000000^3141 ≤ 8014719274631^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120240089 5000000000 8014719274631 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493937717/10000000000 : ℝ)^4165 ≤ (1731209837413/5000000000000 : ℝ)^3141 := by
    have hnat : (4493937717 : ℕ)^4165*5000000000000^3141 ≤ 1731209837413^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493937717 10000000000 1731209837413 5000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873075361/2000000000 : ℝ), (2120240089/5000000000 : ℝ), (4493937717/10000000000 : ℝ)] ![(33316926138749/100000000000000 : ℝ), (8014719274631/25000000000000 : ℝ), (1731209837413/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873075361/2000000000 : ℝ)|^4165 ≤ (33316926138749/100000000000000 : ℝ)^3141
        have hw : |(873075361/2000000000 : ℝ)|=(873075361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120240089/5000000000 : ℝ)|^4165 ≤ (8014719274631/25000000000000 : ℝ)^3141
        have hw : |(2120240089/5000000000 : ℝ)|=(2120240089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493937717/10000000000 : ℝ)|^4165 ≤ (1731209837413/5000000000000 : ℝ)^3141
        have hw : |(4493937717/10000000000 : ℝ)|=(4493937717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433856381/2000000000 : ℝ)*x 0 + (329121899/625000000 : ℝ)*x 1 + (5392832447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433856381/2000000000 : ℝ)^4165 ≤ (6590491857033/50000000000000 : ℝ)^3141 := by
    have hnat : (433856381 : ℕ)^4165*50000000000000^3141 ≤ 6590491857033^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433856381 2000000000 6590491857033 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329121899/625000000 : ℝ)^4165 ≤ (21362160660181/50000000000000 : ℝ)^3141 := by
    have hnat : (329121899 : ℕ)^4165*50000000000000^3141 ≤ 21362160660181^3141*625000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329121899 625000000 21362160660181 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392832447/10000000000 : ℝ)^4165 ≤ (44094694946507/100000000000000 : ℝ)^3141 := by
    have hnat : (5392832447 : ℕ)^4165*100000000000000^3141 ≤ 44094694946507^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392832447 10000000000 44094694946507 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433856381/2000000000 : ℝ), (329121899/625000000 : ℝ), (5392832447/10000000000 : ℝ)] ![(6590491857033/50000000000000 : ℝ), (21362160660181/50000000000000 : ℝ), (44094694946507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433856381/2000000000 : ℝ)|^4165 ≤ (6590491857033/50000000000000 : ℝ)^3141
        have hw : |(-433856381/2000000000 : ℝ)|=(433856381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329121899/625000000 : ℝ)|^4165 ≤ (21362160660181/50000000000000 : ℝ)^3141
        have hw : |(329121899/625000000 : ℝ)|=(329121899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392832447/10000000000 : ℝ)|^4165 ≤ (44094694946507/100000000000000 : ℝ)^3141
        have hw : |(5392832447/10000000000 : ℝ)|=(5392832447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312486769/10000000000 : ℝ)*x 0 + (-1053379319/5000000000 : ℝ)*x 1 + (1348208109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312486769/10000000000 : ℝ)^4165 ≤ (43225695592943/100000000000000 : ℝ)^3141 := by
    have hnat : (5312486769 : ℕ)^4165*100000000000000^3141 ≤ 43225695592943^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312486769 10000000000 43225695592943 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053379319/5000000000 : ℝ)^4165 ≤ (6339804785717/50000000000000 : ℝ)^3141 := by
    have hnat : (1053379319 : ℕ)^4165*50000000000000^3141 ≤ 6339804785717^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053379319 5000000000 6339804785717 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348208109/2500000000 : ℝ)^4165 ≤ (44094694827243/100000000000000 : ℝ)^3141 := by
    have hnat : (1348208109 : ℕ)^4165*100000000000000^3141 ≤ 44094694827243^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348208109 2500000000 44094694827243 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312486769/10000000000 : ℝ), (-1053379319/5000000000 : ℝ), (1348208109/2500000000 : ℝ)] ![(43225695592943/100000000000000 : ℝ), (6339804785717/50000000000000 : ℝ), (44094694827243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312486769/10000000000 : ℝ)|^4165 ≤ (43225695592943/100000000000000 : ℝ)^3141
        have hw : |(5312486769/10000000000 : ℝ)|=(5312486769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053379319/5000000000 : ℝ)|^4165 ≤ (6339804785717/50000000000000 : ℝ)^3141
        have hw : |(-1053379319/5000000000 : ℝ)|=(1053379319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348208109/2500000000 : ℝ)|^4165 ≤ (44094694827243/100000000000000 : ℝ)^3141
        have hw : |(1348208109/2500000000 : ℝ)|=(1348208109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328121691/2500000000 : ℝ)*x 0 + (1078566489/2000000000 : ℝ)*x 1 + (-2106758631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328121691/2500000000 : ℝ)^4165 ≤ (43225695538997/100000000000000 : ℝ)^3141 := by
    have hnat : (1328121691 : ℕ)^4165*100000000000000^3141 ≤ 43225695538997^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328121691 2500000000 43225695538997 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078566489/2000000000 : ℝ)^4165 ≤ (44094694924823/100000000000000 : ℝ)^3141 := by
    have hnat : (1078566489 : ℕ)^4165*100000000000000^3141 ≤ 44094694924823^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078566489 2000000000 44094694924823 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106758631/10000000000 : ℝ)^4165 ≤ (12679609515569/100000000000000 : ℝ)^3141 := by
    have hnat : (2106758631 : ℕ)^4165*100000000000000^3141 ≤ 12679609515569^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106758631 10000000000 12679609515569 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328121691/2500000000 : ℝ), (1078566489/2000000000 : ℝ), (-2106758631/10000000000 : ℝ)] ![(43225695538997/100000000000000 : ℝ), (44094694924823/100000000000000 : ℝ), (12679609515569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328121691/2500000000 : ℝ)|^4165 ≤ (43225695538997/100000000000000 : ℝ)^3141
        have hw : |(1328121691/2500000000 : ℝ)|=(1328121691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078566489/2000000000 : ℝ)|^4165 ≤ (44094694924823/100000000000000 : ℝ)^3141
        have hw : |(1078566489/2000000000 : ℝ)|=(1078566489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106758631/10000000000 : ℝ)|^4165 ≤ (12679609515569/100000000000000 : ℝ)^3141
        have hw : |(-2106758631/10000000000 : ℝ)|=(2106758631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s7_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545673279/1250000000 : ℝ)*x 0 + (4493300763/10000000000 : ℝ)*x 1 + (2120559877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545673279/1250000000 : ℝ)^4165 ≤ (33317021542163/100000000000000 : ℝ)^3141 := by
    have hnat : (545673279 : ℕ)^4165*100000000000000^3141 ≤ 33317021542163^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545673279 1250000000 33317021542163 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493300763/10000000000 : ℝ)^4165 ≤ (34617689494213/100000000000000 : ℝ)^3141 := by
    have hnat : (4493300763 : ℕ)^4165*100000000000000^3141 ≤ 34617689494213^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493300763 10000000000 34617689494213 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120559877/5000000000 : ℝ)^4165 ≤ (32065288945867/100000000000000 : ℝ)^3141 := by
    have hnat : (2120559877 : ℕ)^4165*100000000000000^3141 ≤ 32065288945867^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120559877 5000000000 32065288945867 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545673279/1250000000 : ℝ), (4493300763/10000000000 : ℝ), (2120559877/5000000000 : ℝ)] ![(33317021542163/100000000000000 : ℝ), (34617689494213/100000000000000 : ℝ), (32065288945867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545673279/1250000000 : ℝ)|^4165 ≤ (33317021542163/100000000000000 : ℝ)^3141
        have hw : |(545673279/1250000000 : ℝ)|=(545673279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493300763/10000000000 : ℝ)|^4165 ≤ (34617689494213/100000000000000 : ℝ)^3141
        have hw : |(4493300763/10000000000 : ℝ)|=(4493300763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120559877/5000000000 : ℝ)|^4165 ≤ (32065288945867/100000000000000 : ℝ)^3141
        have hw : |(2120559877/5000000000 : ℝ)|=(2120559877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5673/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11339/100000 : ℝ) ^ (8329/2048 : ℝ) ≤ (7145378632585459/50000000000000000000 : ℝ) := by
    have hpowers : (11339/100000 : ℝ)^8329 ≤ (7145378632585459/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11339 : ℕ)^8329*50000000000000000000^2048 ≤ 7145378632585459^2048*100000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11339 100000 7145378632585459 50000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11339/100000 : ℝ)) (X := (7145378632585459/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (8329/2048 : ℝ) ≤ (17106543977628603/50000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^8329 ≤ (17106543977628603/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7027 : ℕ)^8329*50000000000000000000^2048 ≤ 17106543977628603^2048*50000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 17106543977628603 50000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (17106543977628603/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007145378632585459/25000000000000000000 : ℝ) ≤ (250017567725597/250000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (25007145378632585459/25000000000000000000 : ℝ)^2048 ≤ (250017567725597/250000000000000 : ℝ)^8329 := by
      have hnat : (25007145378632585459 : ℕ)^2048*250000000000000^8329 ≤ 250017567725597^8329*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007145378632585459 25000000000000000000 250017567725597 250000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017567725597/250000000000000 : ℝ)) (X := (25007145378632585459/25000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012125961305107031/25000000000000000000 : ℝ) ≤ (1250149054077549/1250000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (25012125961305107031/25000000000000000000 : ℝ)^2048 ≤ (1250149054077549/1250000000000000 : ℝ)^8329 := by
      have hnat : (25012125961305107031 : ℕ)^2048*1250000000000000^8329 ≤ 1250149054077549^8329*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012125961305107031 25000000000000000000 1250149054077549 1250000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250149054077549/1250000000000000 : ℝ)) (X := (25012125961305107031/25000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017106543977628603/25000000000000000000 : ℝ) ≤ (1250210269527113/1250000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (25017106543977628603/25000000000000000000 : ℝ)^2048 ≤ (1250210269527113/1250000000000000 : ℝ)^8329 := by
      have hnat : (25017106543977628603 : ℕ)^2048*1250000000000000^8329 ≤ 1250210269527113^8329*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017106543977628603 25000000000000000000 1250210269527113 1250000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250210269527113/1250000000000000 : ℝ)) (X := (25017106543977628603/25000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7145378632585459/50000000000000000000 : ℝ) ≤ ((3392600237909766883/3393750000000000000 : ℝ)+2*(15303862391/8484375000000 : ℝ)*(11339/100000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (3392600237909766883/3393750000000000000 : ℝ)+2*(15303862391/8484375000000 : ℝ)*(11339/100000 : ℝ)=(250017567725597/250000000000000 : ℝ) by norm_num, show 1+2*(7145378632585459/50000000000000000000 : ℝ)=(25007145378632585459/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17106543977628603/50000000000000000000 : ℝ)+(7145378632585459/50000000000000000000 : ℝ) ≤ ((3392600237909766883/3393750000000000000 : ℝ)+(15303862391/8484375000000 : ℝ)*((7027/50000 : ℝ)+(11339/100000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (3392600237909766883/3393750000000000000 : ℝ)+(15303862391/8484375000000 : ℝ)*((7027/50000 : ℝ)+(11339/100000 : ℝ))=(1250149054077549/1250000000000000 : ℝ) by norm_num, show 1+(17106543977628603/50000000000000000000 : ℝ)+(7145378632585459/50000000000000000000 : ℝ)=(25012125961305107031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17106543977628603/50000000000000000000 : ℝ) ≤ ((3392600237909766883/3393750000000000000 : ℝ)+2*(15303862391/8484375000000 : ℝ)*(7027/50000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (3392600237909766883/3393750000000000000 : ℝ)+2*(15303862391/8484375000000 : ℝ)*(7027/50000 : ℝ)=(1250210269527113/1250000000000000 : ℝ) by norm_num, show 1+2*(17106543977628603/50000000000000000000 : ℝ)=(25017106543977628603/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3392600237909766883/3393750000000000000 : ℝ)*(X 1 0+X 2 0)+(15303862391/8484375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (3392600237909766883/3393750000000000000 : ℝ)) (alpha := (15303862391/8484375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3392600237909766883/3393750000000000000 : ℝ)*(X 0 1+X 2 1)+(15303862391/8484375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (3392600237909766883/3393750000000000000 : ℝ)) (alpha := (15303862391/8484375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3392600237909766883/3393750000000000000 : ℝ)*(X 0 2+X 1 2)+(15303862391/8484375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (3392600237909766883/3393750000000000000 : ℝ)) (alpha := (15303862391/8484375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-108463869/500000000 : ℝ)*X 0 0+(1348288489/2500000000 : ℝ)*X 0 1+(5265629753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672391801/5000000000 : ℝ)*X 1 0+(-1116980513/5000000000 : ℝ)*X 1 1+(2632815019/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672391883/5000000000 : ℝ)*X 2 0+(5265629827/10000000000 : ℝ)*X 2 1+(-446792217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873075361/2000000000 : ℝ)*X 0 0+(2120240089/5000000000 : ℝ)*X 0 1+(4493937717/10000000000 : ℝ)*X 0 2+(873075361/2000000000 : ℝ)*X 1 0+(2120240089/5000000000 : ℝ)*X 1 1+(4493937717/10000000000 : ℝ)*X 1 2+(873075361/2000000000 : ℝ)*X 2 0+(2120240089/5000000000 : ℝ)*X 2 1+(4493937717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-433856381/2000000000 : ℝ)*X 0 0+(329121899/625000000 : ℝ)*X 0 1+(5392832447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312486769/10000000000 : ℝ)*X 1 0+(-1053379319/5000000000 : ℝ)*X 1 1+(1348208109/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328121691/2500000000 : ℝ)*X 2 0+(1078566489/2000000000 : ℝ)*X 2 1+(-2106758631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545673279/1250000000 : ℝ)*X 0 0+(4493300763/10000000000 : ℝ)*X 0 1+(2120559877/5000000000 : ℝ)*X 0 2+(545673279/1250000000 : ℝ)*X 1 0+(4493300763/10000000000 : ℝ)*X 1 1+(2120559877/5000000000 : ℝ)*X 1 2+(545673279/1250000000 : ℝ)*X 2 0+(4493300763/10000000000 : ℝ)*X 2 1+(2120559877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120015019681439062076337563/56562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1680999397/100000000000000 : ℝ)*(base19) + (823645153/50000000000000 : ℝ)*(base23) + (75876427/20000000000000 : ℝ)*(upper3) + (146621523/100000000000000 : ℝ)*(upper4) + (8104873/6250000000000 : ℝ)*(upper5) + (5893622619875539/100000000000000 : ℝ)*(major0) + (5893622619875539/100000000000000 : ℝ)*(major1) + (5893622619875539/100000000000000 : ℝ)*(major2) + (7841704105857853/100000000000000 : ℝ)*(sp0) + (7841752734733949/100000000000000 : ℝ)*(sp1) + (49010954802769/625000000000 : ℝ)*(sp2) + (986364611629423/25000000000000 : ℝ)*(sp3) + (50309875491/100000000000000 : ℝ)*(sp4) + (8076693237/25000000000000 : ℝ)*(sp7) + (49318634416133/1250000000000 : ℝ)*(f.failure) + (1568350883146669/20000000000000 : ℝ)*(f.sum) + (105244914531107/13575000000000000000000000000 : ℝ)*base66 + (185708406859524979/113125000000000000000000000000000 : ℝ)*base67 + (537817070215774979/113125000000000000000000000000000 : ℝ)*base69 + (713734414645774979/113125000000000000000000000000000 : ℝ)*base71 + (5332358696491/6787500000000000000000000000 : ℝ)*base74 + (2069986050381725021/113125000000000000000000000000000 : ℝ)*base76 + (1643766189042975021/113125000000000000000000000000000 : ℝ)*base78 + (1060130824792024979/113125000000000000000000000000000 : ℝ)*base79 + (1000059149317/3393750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (255413/125000000000000000000 : ℝ)*base89 + (255413/125000000000000000000 : ℝ)*base91 + (255413/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9958495983620917604935119/1767578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (196512347/20000000000000 : ℝ)*(base19) + (270888643/25000000000000 : ℝ)*(base23) + (51306137/50000000000000 : ℝ)*(upper3) + (49832973/100000000000000 : ℝ)*(lower4) + (118485363/100000000000000 : ℝ)*(upper5) + (2961684788512619/50000000000000 : ℝ)*(major0) + (2961684788512619/50000000000000 : ℝ)*(major1) + (2961684788512619/50000000000000 : ℝ)*(major2) + (26839188331/100000000000000 : ℝ)*(sp1) + (29241749109/100000000000000 : ℝ)*(sp2) + (7881334086803783/100000000000000 : ℝ)*(sp4) + (1970326566263429/25000000000000 : ℝ)*(sp5) + (3940651880750051/50000000000000 : ℝ)*(sp6) + (3965404879447423/100000000000000 : ℝ)*(sp7) + (3965404879447423/100000000000000 : ℝ)*(f.failure) + (7881334086803783/100000000000000 : ℝ)*(f.sum) + (45238152722281/13575000000000000000000000000 : ℝ)*base65 + (604766903636013641/56562500000000000000000000000000 : ℝ)*base68 + (3663331286638641/56562500000000000000000000000000 : ℝ)*base70 + (150414555688673859/56562500000000000000000000000000 : ℝ)*base71 + (48568591447231/13575000000000000000000000000 : ℝ)*base73 + (1061103327315701141/56562500000000000000000000000000 : ℝ)*base76 + (191504770135076141/56562500000000000000000000000000 : ℝ)*base78 + (1369264571086326141/56562500000000000000000000000000 : ℝ)*base80 + (76871204243731/13575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (49083103/10000000000000000000000 : ℝ)*base89 + (49083103/10000000000000000000000 : ℝ)*base91 + (49083103/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1137_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1137_s8_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2169282103/10000000000 : ℝ)*x 0 + (5393083679/10000000000 : ℝ)*x 1 + (2632848521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169282103/10000000000 : ℝ)^4165 ≤ (3295246327343/25000000000000 : ℝ)^3141 := by
    have hnat : (2169282103 : ℕ)^4165*25000000000000^3141 ≤ 3295246327343^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169282103 10000000000 3295246327343 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393083679/10000000000 : ℝ)^4165 ≤ (5512177358619/12500000000000 : ℝ)^3141 := by
    have hnat : (5393083679 : ℕ)^4165*12500000000000^3141 ≤ 5512177358619^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393083679 10000000000 5512177358619 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632848521/5000000000 : ℝ)^4165 ≤ (21360797900511/50000000000000 : ℝ)^3141 := by
    have hnat : (2632848521 : ℕ)^4165*50000000000000^3141 ≤ 21360797900511^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632848521 5000000000 21360797900511 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2169282103/10000000000 : ℝ), (5393083679/10000000000 : ℝ), (2632848521/5000000000 : ℝ)] ![(3295246327343/25000000000000 : ℝ), (5512177358619/12500000000000 : ℝ), (21360797900511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2169282103/10000000000 : ℝ)|^4165 ≤ (3295246327343/25000000000000 : ℝ)^3141
        have hw : |(-2169282103/10000000000 : ℝ)|=(2169282103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393083679/10000000000 : ℝ)|^4165 ≤ (5512177358619/12500000000000 : ℝ)^3141
        have hw : |(5393083679/10000000000 : ℝ)|=(5393083679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632848521/5000000000 : ℝ)|^4165 ≤ (21360797900511/50000000000000 : ℝ)^3141
        have hw : |(2632848521/5000000000 : ℝ)|=(2632848521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534476623/1000000000 : ℝ)*x 0 + (-2233895497/10000000000 : ℝ)*x 1 + (2632848521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534476623/1000000000 : ℝ)^4165 ≤ (5446788899379/12500000000000 : ℝ)^3141 := by
    have hnat : (534476623 : ℕ)^4165*12500000000000^3141 ≤ 5446788899379^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534476623 1000000000 5446788899379 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233895497/10000000000 : ℝ)^4165 ≤ (13704092978963/100000000000000 : ℝ)^3141 := by
    have hnat : (2233895497 : ℕ)^4165*100000000000000^3141 ≤ 13704092978963^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233895497 10000000000 13704092978963 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632848521/5000000000 : ℝ)^4165 ≤ (21360797900511/50000000000000 : ℝ)^3141 := by
    have hnat : (2632848521 : ℕ)^4165*50000000000000^3141 ≤ 21360797900511^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632848521 5000000000 21360797900511 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534476623/1000000000 : ℝ), (-2233895497/10000000000 : ℝ), (2632848521/5000000000 : ℝ)] ![(5446788899379/12500000000000 : ℝ), (13704092978963/100000000000000 : ℝ), (21360797900511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534476623/1000000000 : ℝ)|^4165 ≤ (5446788899379/12500000000000 : ℝ)^3141
        have hw : |(534476623/1000000000 : ℝ)|=(534476623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233895497/10000000000 : ℝ)|^4165 ≤ (13704092978963/100000000000000 : ℝ)^3141
        have hw : |(-2233895497/10000000000 : ℝ)|=(2233895497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632848521/5000000000 : ℝ)|^4165 ≤ (21360797900511/50000000000000 : ℝ)^3141
        have hw : |(2632848521/5000000000 : ℝ)|=(2632848521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534476623/1000000000 : ℝ)*x 0 + (5265697043/10000000000 : ℝ)*x 1 + (-1116947749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534476623/1000000000 : ℝ)^4165 ≤ (5446788899379/12500000000000 : ℝ)^3141 := by
    have hnat : (534476623 : ℕ)^4165*12500000000000^3141 ≤ 5446788899379^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534476623 1000000000 5446788899379 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265697043/10000000000 : ℝ)^4165 ≤ (2136079790589/5000000000000 : ℝ)^3141 := by
    have hnat : (5265697043 : ℕ)^4165*5000000000000^3141 ≤ 2136079790589^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265697043 10000000000 2136079790589 5000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116947749/5000000000 : ℝ)^4165 ≤ (6852046493549/50000000000000 : ℝ)^3141 := by
    have hnat : (1116947749 : ℕ)^4165*50000000000000^3141 ≤ 6852046493549^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116947749 5000000000 6852046493549 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534476623/1000000000 : ℝ), (5265697043/10000000000 : ℝ), (-1116947749/5000000000 : ℝ)] ![(5446788899379/12500000000000 : ℝ), (2136079790589/5000000000000 : ℝ), (6852046493549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534476623/1000000000 : ℝ)|^4165 ≤ (5446788899379/12500000000000 : ℝ)^3141
        have hw : |(534476623/1000000000 : ℝ)|=(534476623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265697043/10000000000 : ℝ)|^4165 ≤ (2136079790589/5000000000000 : ℝ)^3141
        have hw : |(5265697043/10000000000 : ℝ)|=(5265697043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1116947749/5000000000 : ℝ)|^4165 ≤ (6852046493549/50000000000000 : ℝ)^3141
        have hw : |(-1116947749/5000000000 : ℝ)|=(1116947749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365379981/10000000000 : ℝ)*x 0 + (2120308353/5000000000 : ℝ)*x 1 + (2246900301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365379981/10000000000 : ℝ)^4165 ≤ (16658479140297/50000000000000 : ℝ)^3141 := by
    have hnat : (4365379981 : ℕ)^4165*50000000000000^3141 ≤ 16658479140297^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365379981 10000000000 16658479140297 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120308353/5000000000 : ℝ)^4165 ≤ (16030122893083/50000000000000 : ℝ)^3141 := by
    have hnat : (2120308353 : ℕ)^4165*50000000000000^3141 ≤ 16030122893083^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120308353 5000000000 16030122893083 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246900301/5000000000 : ℝ)^4165 ≤ (3462279592761/10000000000000 : ℝ)^3141 := by
    have hnat : (2246900301 : ℕ)^4165*10000000000000^3141 ≤ 3462279592761^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246900301 5000000000 3462279592761 10000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365379981/10000000000 : ℝ), (2120308353/5000000000 : ℝ), (2246900301/5000000000 : ℝ)] ![(16658479140297/50000000000000 : ℝ), (16030122893083/50000000000000 : ℝ), (3462279592761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365379981/10000000000 : ℝ)|^4165 ≤ (16658479140297/50000000000000 : ℝ)^3141
        have hw : |(4365379981/10000000000 : ℝ)|=(4365379981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120308353/5000000000 : ℝ)|^4165 ≤ (16030122893083/50000000000000 : ℝ)^3141
        have hw : |(2120308353/5000000000 : ℝ)|=(2120308353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246900301/5000000000 : ℝ)|^4165 ≤ (3462279592761/10000000000000 : ℝ)^3141
        have hw : |(2246900301/5000000000 : ℝ)|=(2246900301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216928699/1000000000 : ℝ)*x 0 + (5266016847/10000000000 : ℝ)*x 1 + (5392762719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216928699/1000000000 : ℝ)^4165 ≤ (411907021389/3125000000000 : ℝ)^3141 := by
    have hnat : (216928699 : ℕ)^4165*3125000000000^3141 ≤ 411907021389^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216928699 1000000000 411907021389 3125000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266016847/10000000000 : ℝ)^4165 ≤ (5340629544217/12500000000000 : ℝ)^3141 := by
    have hnat : (5266016847 : ℕ)^4165*12500000000000^3141 ≤ 5340629544217^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266016847 10000000000 5340629544217 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392762719/10000000000 : ℝ)^4165 ≤ (44093938944797/100000000000000 : ℝ)^3141 := by
    have hnat : (5392762719 : ℕ)^4165*100000000000000^3141 ≤ 44093938944797^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392762719 10000000000 44093938944797 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216928699/1000000000 : ℝ), (5266016847/10000000000 : ℝ), (5392762719/10000000000 : ℝ)] ![(411907021389/3125000000000 : ℝ), (5340629544217/12500000000000 : ℝ), (44093938944797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216928699/1000000000 : ℝ)|^4165 ≤ (411907021389/3125000000000 : ℝ)^3141
        have hw : |(-216928699/1000000000 : ℝ)|=(216928699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266016847/10000000000 : ℝ)|^4165 ≤ (5340629544217/12500000000000 : ℝ)^3141
        have hw : |(5266016847/10000000000 : ℝ)|=(5266016847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392762719/10000000000 : ℝ)|^4165 ≤ (44093938944797/100000000000000 : ℝ)^3141
        have hw : |(5392762719/10000000000 : ℝ)|=(5392762719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656252087/5000000000 : ℝ)*x 0 + (-2106829821/10000000000 : ℝ)*x 1 + (5392762719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656252087/5000000000 : ℝ)^4165 ≤ (8645176675983/20000000000000 : ℝ)^3141 := by
    have hnat : (2656252087 : ℕ)^4165*20000000000000^3141 ≤ 8645176675983^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656252087 5000000000 8645176675983 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106829821/10000000000 : ℝ)^4165 ≤ (3170044415261/25000000000000 : ℝ)^3141 := by
    have hnat : (2106829821 : ℕ)^4165*25000000000000^3141 ≤ 3170044415261^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106829821 10000000000 3170044415261 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392762719/10000000000 : ℝ)^4165 ≤ (44093938944797/100000000000000 : ℝ)^3141 := by
    have hnat : (5392762719 : ℕ)^4165*100000000000000^3141 ≤ 44093938944797^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392762719 10000000000 44093938944797 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656252087/5000000000 : ℝ), (-2106829821/10000000000 : ℝ), (5392762719/10000000000 : ℝ)] ![(8645176675983/20000000000000 : ℝ), (3170044415261/25000000000000 : ℝ), (44093938944797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656252087/5000000000 : ℝ)|^4165 ≤ (8645176675983/20000000000000 : ℝ)^3141
        have hw : |(2656252087/5000000000 : ℝ)|=(2656252087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106829821/10000000000 : ℝ)|^4165 ≤ (3170044415261/25000000000000 : ℝ)^3141
        have hw : |(-2106829821/10000000000 : ℝ)|=(2106829821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392762719/10000000000 : ℝ)|^4165 ≤ (44093938944797/100000000000000 : ℝ)^3141
        have hw : |(5392762719/10000000000 : ℝ)|=(5392762719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656252087/5000000000 : ℝ)*x 0 + (5392762719/10000000000 : ℝ)*x 1 + (-2106829821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656252087/5000000000 : ℝ)^4165 ≤ (8645176675983/20000000000000 : ℝ)^3141 := by
    have hnat : (2656252087 : ℕ)^4165*20000000000000^3141 ≤ 8645176675983^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656252087 5000000000 8645176675983 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392762719/10000000000 : ℝ)^4165 ≤ (44093938944797/100000000000000 : ℝ)^3141 := by
    have hnat : (5392762719 : ℕ)^4165*100000000000000^3141 ≤ 44093938944797^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392762719 10000000000 44093938944797 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106829821/10000000000 : ℝ)^4165 ≤ (3170044415261/25000000000000 : ℝ)^3141 := by
    have hnat : (2106829821 : ℕ)^4165*25000000000000^3141 ≤ 3170044415261^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106829821 10000000000 3170044415261 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656252087/5000000000 : ℝ), (5392762719/10000000000 : ℝ), (-2106829821/10000000000 : ℝ)] ![(8645176675983/20000000000000 : ℝ), (44093938944797/100000000000000 : ℝ), (3170044415261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656252087/5000000000 : ℝ)|^4165 ≤ (8645176675983/20000000000000 : ℝ)^3141
        have hw : |(2656252087/5000000000 : ℝ)|=(2656252087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392762719/10000000000 : ℝ)|^4165 ≤ (44093938944797/100000000000000 : ℝ)^3141
        have hw : |(5392762719/10000000000 : ℝ)|=(5392762719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106829821/10000000000 : ℝ)|^4165 ≤ (3170044415261/25000000000000 : ℝ)^3141
        have hw : |(-2106829821/10000000000 : ℝ)|=(2106829821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s8_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365389693/10000000000 : ℝ)*x 0 + (561645623/1250000000 : ℝ)*x 1 + (4241254619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365389693/10000000000 : ℝ)^4165 ≤ (16658528284149/50000000000000 : ℝ)^3141 := by
    have hnat : (4365389693 : ℕ)^4165*50000000000000^3141 ≤ 16658528284149^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365389693 10000000000 16658528284149 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561645623/1250000000 : ℝ)^4165 ≤ (17308151193349/50000000000000 : ℝ)^3141 := by
    have hnat : (561645623 : ℕ)^4165*50000000000000^3141 ≤ 17308151193349^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561645623 1250000000 17308151193349 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241254619/10000000000 : ℝ)^4165 ≤ (32066641028391/100000000000000 : ℝ)^3141 := by
    have hnat : (4241254619 : ℕ)^4165*100000000000000^3141 ≤ 32066641028391^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241254619 10000000000 32066641028391 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365389693/10000000000 : ℝ), (561645623/1250000000 : ℝ), (4241254619/10000000000 : ℝ)] ![(16658528284149/50000000000000 : ℝ), (17308151193349/50000000000000 : ℝ), (32066641028391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365389693/10000000000 : ℝ)|^4165 ≤ (16658528284149/50000000000000 : ℝ)^3141
        have hw : |(4365389693/10000000000 : ℝ)|=(4365389693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561645623/1250000000 : ℝ)|^4165 ≤ (17308151193349/50000000000000 : ℝ)^3141
        have hw : |(561645623/1250000000 : ℝ)|=(561645623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241254619/10000000000 : ℝ)|^4165 ≤ (32066641028391/100000000000000 : ℝ)^3141
        have hw : |(4241254619/10000000000 : ℝ)|=(4241254619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5673/50000 : ℝ) ^ (8329/2048 : ℝ) ≤ (14326670336224743/100000000000000000000 : ℝ) := by
    have hpowers : (5673/50000 : ℝ)^8329 ≤ (14326670336224743/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5673 : ℕ)^8329*100000000000000000000^2048 ≤ 14326670336224743^2048*50000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5673 50000 14326670336224743 100000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5673/50000 : ℝ)) (X := (14326670336224743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/100000 : ℝ) ^ (8329/2048 : ℝ) ≤ (17071918835755551/50000000000000000000 : ℝ) := by
    have hpowers : (14047/100000 : ℝ)^8329 ≤ (17071918835755551/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14047 : ℕ)^8329*50000000000000000000^2048 ≤ 17071918835755551^2048*100000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 100000 17071918835755551 50000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/100000 : ℝ)) (X := (17071918835755551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014326670336224743/50000000000000000000 : ℝ) ≤ (2500176118690121/2500000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (50014326670336224743/50000000000000000000 : ℝ)^2048 ≤ (2500176118690121/2500000000000000 : ℝ)^8329 := by
      have hnat : (50014326670336224743 : ℕ)^2048*2500000000000000^8329 ≤ 2500176118690121^8329*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014326670336224743 50000000000000000000 2500176118690121 2500000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500176118690121/2500000000000000 : ℝ)) (X := (50014326670336224743/50000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009694101601547169/20000000000000000000 : ℝ) ≤ (6250744758249/6250000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (20009694101601547169/20000000000000000000 : ℝ)^2048 ≤ (6250744758249/6250000000000 : ℝ)^8329 := by
      have hnat : (20009694101601547169 : ℕ)^2048*6250000000000^8329 ≤ 6250744758249^8329*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009694101601547169 20000000000000000000 6250744758249 6250000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6250744758249/6250000000000 : ℝ)) (X := (20009694101601547169/20000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017071918835755551/25000000000000000000 : ℝ) ≤ (2500419687909079/2500000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (25017071918835755551/25000000000000000000 : ℝ)^2048 ≤ (2500419687909079/2500000000000000 : ℝ)^8329 := by
      have hnat : (25017071918835755551 : ℕ)^2048*2500000000000000^8329 ≤ 2500419687909079^8329*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017071918835755551 25000000000000000000 2500419687909079 2500000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500419687909079/2500000000000000 : ℝ)) (X := (25017071918835755551/25000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14326670336224743/100000000000000000000 : ℝ) ≤ ((6750212160223719353/6752500000000000000 : ℝ)+2*(121784609479/67525000000000 : ℝ)*(5673/50000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (6750212160223719353/6752500000000000000 : ℝ)+2*(121784609479/67525000000000 : ℝ)*(5673/50000 : ℝ)=(2500176118690121/2500000000000000 : ℝ) by norm_num, show 1+2*(14326670336224743/100000000000000000000 : ℝ)=(50014326670336224743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17071918835755551/50000000000000000000 : ℝ)+(14326670336224743/100000000000000000000 : ℝ) ≤ ((6750212160223719353/6752500000000000000 : ℝ)+(121784609479/67525000000000 : ℝ)*((14047/100000 : ℝ)+(5673/50000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (6750212160223719353/6752500000000000000 : ℝ)+(121784609479/67525000000000 : ℝ)*((14047/100000 : ℝ)+(5673/50000 : ℝ))=(6250744758249/6250000000000 : ℝ) by norm_num, show 1+(17071918835755551/50000000000000000000 : ℝ)+(14326670336224743/100000000000000000000 : ℝ)=(20009694101601547169/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17071918835755551/50000000000000000000 : ℝ) ≤ ((6750212160223719353/6752500000000000000 : ℝ)+2*(121784609479/67525000000000 : ℝ)*(14047/100000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (6750212160223719353/6752500000000000000 : ℝ)+2*(121784609479/67525000000000 : ℝ)*(14047/100000 : ℝ)=(2500419687909079/2500000000000000 : ℝ) by norm_num, show 1+2*(17071918835755551/50000000000000000000 : ℝ)=(25017071918835755551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6750212160223719353/6752500000000000000 : ℝ)*(X 1 0+X 2 0)+(121784609479/67525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (6750212160223719353/6752500000000000000 : ℝ)) (alpha := (121784609479/67525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6750212160223719353/6752500000000000000 : ℝ)*(X 0 1+X 2 1)+(121784609479/67525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (6750212160223719353/6752500000000000000 : ℝ)) (alpha := (121784609479/67525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6750212160223719353/6752500000000000000 : ℝ)*(X 0 2+X 1 2)+(121784609479/67525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (6750212160223719353/6752500000000000000 : ℝ)) (alpha := (121784609479/67525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2169282103/10000000000 : ℝ)*X 0 0+(5393083679/10000000000 : ℝ)*X 0 1+(2632848521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534476623/1000000000 : ℝ)*X 1 0+(-2233895497/10000000000 : ℝ)*X 1 1+(2632848521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534476623/1000000000 : ℝ)*X 2 0+(5265697043/10000000000 : ℝ)*X 2 1+(-1116947749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365379981/10000000000 : ℝ)*X 0 0+(2120308353/5000000000 : ℝ)*X 0 1+(2246900301/5000000000 : ℝ)*X 0 2+(4365379981/10000000000 : ℝ)*X 1 0+(2120308353/5000000000 : ℝ)*X 1 1+(2246900301/5000000000 : ℝ)*X 1 2+(4365379981/10000000000 : ℝ)*X 2 0+(2120308353/5000000000 : ℝ)*X 2 1+(2246900301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-216928699/1000000000 : ℝ)*X 0 0+(5266016847/10000000000 : ℝ)*X 0 1+(5392762719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656252087/5000000000 : ℝ)*X 1 0+(-2106829821/10000000000 : ℝ)*X 1 1+(5392762719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656252087/5000000000 : ℝ)*X 2 0+(5392762719/10000000000 : ℝ)*X 2 1+(-2106829821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365389693/10000000000 : ℝ)*X 0 0+(561645623/1250000000 : ℝ)*X 0 1+(4241254619/10000000000 : ℝ)*X 0 2+(4365389693/10000000000 : ℝ)*X 1 0+(561645623/1250000000 : ℝ)*X 1 1+(4241254619/10000000000 : ℝ)*X 1 2+(4365389693/10000000000 : ℝ)*X 2 0+(561645623/1250000000 : ℝ)*X 2 1+(4241254619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15167034330868635492117/1688125000000000000000000000 : ℝ) := by norm_num
    linear_combination (888700221/50000000000000 : ℝ)*(base19) + (8273107/500000000000 : ℝ)*(base23) + (128169/195312500000 : ℝ)*(lower2) + (1420187/625000000000 : ℝ)*(upper3) + (68177721/50000000000000 : ℝ)*(upper5) + (5899982284998777/100000000000000 : ℝ)*(major0) + (5899982284998777/100000000000000 : ℝ)*(major1) + (5899982284998777/100000000000000 : ℝ)*(major2) + (7850167693140023/100000000000000 : ℝ)*(sp0) + (3925107128255973/50000000000000 : ℝ)*(sp1) + (1962553594822747/25000000000000 : ℝ)*(sp2) + (1974860978791729/50000000000000 : ℝ)*(sp3) + (9668154473/20000000000000 : ℝ)*(sp4) + (26279016877/100000000000000 : ℝ)*(sp7) + (1974874118300167/50000000000000 : ℝ)*(f.failure) + (1962554008478097/25000000000000 : ℝ)*(f.sum) + (867589623623/844062500000000000000000000 : ℝ)*base66 + (12818880733792531281/675250000000000000000000000000000 : ℝ)*base67 + (2947205297530468719/675250000000000000000000000000000 : ℝ)*base70 + (818390309270218719/675250000000000000000000000000000 : ℝ)*base72 + (47325655981981/6752500000000000000000000000 : ℝ)*base73 + (4871324318788218719/675250000000000000000000000000000 : ℝ)*base76 + (914738982314781281/675250000000000000000000000000000 : ℝ)*base77 + (8387126720514531281/675250000000000000000000000000000 : ℝ)*base79 + (38863134436543/13505000000000000000000000000 : ℝ)*base82 + (57881113/5000000000000000000000 : ℝ)*base90 + (57881113/5000000000000000000000 : ℝ)*base92 + (57881113/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425011547917531736442019881/42203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1843335541/100000000000000 : ℝ)*(base19) + (6262671/312500000000 : ℝ)*(base23) + (323457253/50000000000000 : ℝ)*(lower1) + (20235391/10000000000000 : ℝ)*(upper3) + (1461403/2000000000000 : ℝ)*(lower4) + (205418983/100000000000000 : ℝ)*(upper5) + (1482423800135841/25000000000000 : ℝ)*(major0) + (1482423800135841/25000000000000 : ℝ)*(major1) + (1482423800135841/25000000000000 : ℝ)*(major2) + (1908125067/50000000000000 : ℝ)*(sp2) + (3944875245912123/50000000000000 : ℝ)*(sp4) + (1577949729697741/20000000000000 : ℝ)*(sp5) + (246554520984981/3125000000000 : ℝ)*(sp6) + (3969639573575173/100000000000000 : ℝ)*(sp7) + (3969639573575173/100000000000000 : ℝ)*(f.failure) + (3944875245912123/50000000000000 : ℝ)*(f.sum) + (45159609583821/13505000000000000000000000000 : ℝ)*base66 + (13853557324194905873/168812500000000000000000000000000 : ℝ)*base67 + (198053490740718373/168812500000000000000000000000000 : ℝ)*base69 + (45733893840603343373/168812500000000000000000000000000 : ℝ)*base71 + (66485869327211/13505000000000000000000000000 : ℝ)*base74 + (10924580781804344127/168812500000000000000000000000000 : ℝ)*base76 + (786930582543468373/168812500000000000000000000000000 : ℝ)*base77 + (514630293079405873/168812500000000000000000000000000 : ℝ)*base79 + (13281815713691/13505000000000000000000000000 : ℝ)*base82 + (12349147/10000000000000000000000 : ℝ)*base90 + (12349147/10000000000000000000000 : ℝ)*base92 + (12349147/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1137_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1137_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1137_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1137_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1137_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1137_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

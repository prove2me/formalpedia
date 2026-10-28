-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1149_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:35:10.971099+00:00
-- url     : https://prove2.me/submissions/f7f086b5-8869-4d8e-b623-2c5e6e6ede9f

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
theorem support_rectangle_w1149_s6_0 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081756977/5000000000 : ℝ)*x 0 + (5393244921/10000000000 : ℝ)*x 1 + (2632766733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081756977/5000000000 : ℝ)^4171 ≤ (6573517329239/50000000000000 : ℝ)^3147 := by
    have hnat : (1081756977 : ℕ)^4171*50000000000000^3147 ≤ 6573517329239^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081756977 5000000000 6573517329239 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393244921/10000000000 : ℝ)^4171 ≤ (44116094645169/100000000000000 : ℝ)^3147 := by
    have hnat : (5393244921 : ℕ)^4171*100000000000000^3147 ≤ 44116094645169^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393244921 10000000000 44116094645169 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632766733/5000000000 : ℝ)^4171 ≤ (42736870688277/100000000000000 : ℝ)^3147 := by
    have hnat : (2632766733 : ℕ)^4171*100000000000000^3147 ≤ 42736870688277^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632766733 5000000000 42736870688277 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081756977/5000000000 : ℝ), (5393244921/10000000000 : ℝ), (2632766733/5000000000 : ℝ)] ![(6573517329239/50000000000000 : ℝ), (44116094645169/100000000000000 : ℝ), (42736870688277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081756977/5000000000 : ℝ)|^4171 ≤ (6573517329239/50000000000000 : ℝ)^3147
        have hw : |(-1081756977/5000000000 : ℝ)|=(1081756977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393244921/10000000000 : ℝ)|^4171 ≤ (44116094645169/100000000000000 : ℝ)^3147
        have hw : |(5393244921/10000000000 : ℝ)|=(5393244921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632766733/5000000000 : ℝ)|^4171 ≤ (42736870688277/100000000000000 : ℝ)^3147
        have hw : |(2632766733/5000000000 : ℝ)|=(2632766733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_1 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344816789/10000000000 : ℝ)*x 0 + (-1114147191/5000000000 : ℝ)*x 1 + (2632766733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344816789/10000000000 : ℝ)^4171 ≤ (871836568689/2000000000000 : ℝ)^3147 := by
    have hnat : (5344816789 : ℕ)^4171*2000000000000^3147 ≤ 871836568689^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344816789 10000000000 871836568689 2000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114147191/5000000000 : ℝ)^4171 ≤ (3417825217589/25000000000000 : ℝ)^3147 := by
    have hnat : (1114147191 : ℕ)^4171*25000000000000^3147 ≤ 3417825217589^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114147191 5000000000 3417825217589 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632766733/5000000000 : ℝ)^4171 ≤ (42736870688277/100000000000000 : ℝ)^3147 := by
    have hnat : (2632766733 : ℕ)^4171*100000000000000^3147 ≤ 42736870688277^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632766733 5000000000 42736870688277 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344816789/10000000000 : ℝ), (-1114147191/5000000000 : ℝ), (2632766733/5000000000 : ℝ)] ![(871836568689/2000000000000 : ℝ), (3417825217589/25000000000000 : ℝ), (42736870688277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344816789/10000000000 : ℝ)|^4171 ≤ (871836568689/2000000000000 : ℝ)^3147
        have hw : |(5344816789/10000000000 : ℝ)|=(5344816789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114147191/5000000000 : ℝ)|^4171 ≤ (3417825217589/25000000000000 : ℝ)^3147
        have hw : |(-1114147191/5000000000 : ℝ)|=(1114147191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632766733/5000000000 : ℝ)|^4171 ≤ (42736870688277/100000000000000 : ℝ)^3147
        have hw : |(2632766733/5000000000 : ℝ)|=(2632766733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_2 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344816789/10000000000 : ℝ)*x 0 + (2632766733/5000000000 : ℝ)*x 1 + (-1114147191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344816789/10000000000 : ℝ)^4171 ≤ (871836568689/2000000000000 : ℝ)^3147 := by
    have hnat : (5344816789 : ℕ)^4171*2000000000000^3147 ≤ 871836568689^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344816789 10000000000 871836568689 2000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632766733/5000000000 : ℝ)^4171 ≤ (42736870688277/100000000000000 : ℝ)^3147 := by
    have hnat : (2632766733 : ℕ)^4171*100000000000000^3147 ≤ 42736870688277^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632766733 5000000000 42736870688277 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114147191/5000000000 : ℝ)^4171 ≤ (3417825217589/25000000000000 : ℝ)^3147 := by
    have hnat : (1114147191 : ℕ)^4171*25000000000000^3147 ≤ 3417825217589^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114147191 5000000000 3417825217589 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344816789/10000000000 : ℝ), (2632766733/5000000000 : ℝ), (-1114147191/5000000000 : ℝ)] ![(871836568689/2000000000000 : ℝ), (42736870688277/100000000000000 : ℝ), (3417825217589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344816789/10000000000 : ℝ)|^4171 ≤ (871836568689/2000000000000 : ℝ)^3147
        have hw : |(5344816789/10000000000 : ℝ)|=(5344816789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632766733/5000000000 : ℝ)|^4171 ≤ (42736870688277/100000000000000 : ℝ)^3147
        have hw : |(2632766733/5000000000 : ℝ)|=(2632766733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114147191/5000000000 : ℝ)|^4171 ≤ (3417825217589/25000000000000 : ℝ)^3147
        have hw : |(-1114147191/5000000000 : ℝ)|=(1114147191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_3 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545458901/1250000000 : ℝ)*x 0 + (264893727/625000000 : ℝ)*x 1 + (1123181793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545458901/1250000000 : ℝ)^4171 ≤ (8329208703573/25000000000000 : ℝ)^3147 := by
    have hnat : (545458901 : ℕ)^4171*25000000000000^3147 ≤ 8329208703573^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545458901 1250000000 8329208703573 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264893727/625000000 : ℝ)^4171 ≤ (8013529393523/25000000000000 : ℝ)^3147 := by
    have hnat : (264893727 : ℕ)^4171*25000000000000^3147 ≤ 8013529393523^3147*625000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264893727 625000000 8013529393523 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123181793/2500000000 : ℝ)^4171 ≤ (34629047602023/100000000000000 : ℝ)^3147 := by
    have hnat : (1123181793 : ℕ)^4171*100000000000000^3147 ≤ 34629047602023^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123181793 2500000000 34629047602023 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545458901/1250000000 : ℝ), (264893727/625000000 : ℝ), (1123181793/2500000000 : ℝ)] ![(8329208703573/25000000000000 : ℝ), (8013529393523/25000000000000 : ℝ), (34629047602023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545458901/1250000000 : ℝ)|^4171 ≤ (8329208703573/25000000000000 : ℝ)^3147
        have hw : |(545458901/1250000000 : ℝ)|=(545458901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264893727/625000000 : ℝ)|^4171 ≤ (8013529393523/25000000000000 : ℝ)^3147
        have hw : |(264893727/625000000 : ℝ)|=(264893727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123181793/2500000000 : ℝ)|^4171 ≤ (34629047602023/100000000000000 : ℝ)^3147
        have hw : |(1123181793/2500000000 : ℝ)|=(1123181793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_4 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163518931/10000000000 : ℝ)*x 0 + (526585603/1000000000 : ℝ)*x 1 + (2696460579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163518931/10000000000 : ℝ)^4171 ≤ (3286768685811/25000000000000 : ℝ)^3147 := by
    have hnat : (2163518931 : ℕ)^4171*25000000000000^3147 ≤ 3286768685811^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163518931 10000000000 3286768685811 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526585603/1000000000 : ℝ)^4171 ≤ (10685085161159/25000000000000 : ℝ)^3147 := by
    have hnat : (526585603 : ℕ)^4171*25000000000000^3147 ≤ 10685085161159^3147*1000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526585603 1000000000 10685085161159 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696460579/5000000000 : ℝ)^4171 ≤ (44112584594891/100000000000000 : ℝ)^3147 := by
    have hnat : (2696460579 : ℕ)^4171*100000000000000^3147 ≤ 44112584594891^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696460579 5000000000 44112584594891 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163518931/10000000000 : ℝ), (526585603/1000000000 : ℝ), (2696460579/5000000000 : ℝ)] ![(3286768685811/25000000000000 : ℝ), (10685085161159/25000000000000 : ℝ), (44112584594891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163518931/10000000000 : ℝ)|^4171 ≤ (3286768685811/25000000000000 : ℝ)^3147
        have hw : |(-2163518931/10000000000 : ℝ)|=(2163518931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526585603/1000000000 : ℝ)|^4171 ≤ (10685085161159/25000000000000 : ℝ)^3147
        have hw : |(526585603/1000000000 : ℝ)|=(526585603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696460579/5000000000 : ℝ)|^4171 ≤ (44112584594891/100000000000000 : ℝ)^3147
        have hw : |(2696460579/5000000000 : ℝ)|=(2696460579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_5 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312443837/10000000000 : ℝ)*x 0 + (-2100906673/10000000000 : ℝ)*x 1 + (5392921149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312443837/10000000000 : ℝ)^4171 ≤ (2162111509093/5000000000000 : ℝ)^3147 := by
    have hnat : (5312443837 : ℕ)^4171*5000000000000^3147 ≤ 2162111509093^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312443837 10000000000 2162111509093 5000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100906673/10000000000 : ℝ)^4171 ≤ (12645185305399/100000000000000 : ℝ)^3147 := by
    have hnat : (2100906673 : ℕ)^4171*100000000000000^3147 ≤ 12645185305399^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100906673 10000000000 12645185305399 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392921149/10000000000 : ℝ)^4171 ≤ (44112584497319/100000000000000 : ℝ)^3147 := by
    have hnat : (5392921149 : ℕ)^4171*100000000000000^3147 ≤ 44112584497319^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392921149 10000000000 44112584497319 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312443837/10000000000 : ℝ), (-2100906673/10000000000 : ℝ), (5392921149/10000000000 : ℝ)] ![(2162111509093/5000000000000 : ℝ), (12645185305399/100000000000000 : ℝ), (44112584497319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312443837/10000000000 : ℝ)|^4171 ≤ (2162111509093/5000000000000 : ℝ)^3147
        have hw : |(5312443837/10000000000 : ℝ)|=(5312443837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100906673/10000000000 : ℝ)|^4171 ≤ (12645185305399/100000000000000 : ℝ)^3147
        have hw : |(-2100906673/10000000000 : ℝ)|=(2100906673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392921149/10000000000 : ℝ)|^4171 ≤ (44112584497319/100000000000000 : ℝ)^3147
        have hw : |(5392921149/10000000000 : ℝ)|=(5392921149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_6 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062488767/2000000000 : ℝ)*x 0 + (5392921129/10000000000 : ℝ)*x 1 + (-2100906703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062488767/2000000000 : ℝ)^4171 ≤ (43242230160283/100000000000000 : ℝ)^3147 := by
    have hnat : (1062488767 : ℕ)^4171*100000000000000^3147 ≤ 43242230160283^3147*2000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062488767 2000000000 43242230160283 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392921129/10000000000 : ℝ)^4171 ≤ (44112584280493/100000000000000 : ℝ)^3147 := by
    have hnat : (5392921129 : ℕ)^4171*100000000000000^3147 ≤ 44112584280493^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392921129 10000000000 44112584280493 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100906703/10000000000 : ℝ)^4171 ≤ (6322592772361/50000000000000 : ℝ)^3147 := by
    have hnat : (2100906703 : ℕ)^4171*50000000000000^3147 ≤ 6322592772361^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100906703 10000000000 6322592772361 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062488767/2000000000 : ℝ), (5392921129/10000000000 : ℝ), (-2100906703/10000000000 : ℝ)] ![(43242230160283/100000000000000 : ℝ), (44112584280493/100000000000000 : ℝ), (6322592772361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062488767/2000000000 : ℝ)|^4171 ≤ (43242230160283/100000000000000 : ℝ)^3147
        have hw : |(1062488767/2000000000 : ℝ)|=(1062488767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392921129/10000000000 : ℝ)|^4171 ≤ (44112584280493/100000000000000 : ℝ)^3147
        have hw : |(5392921129/10000000000 : ℝ)|=(5392921129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100906703/10000000000 : ℝ)|^4171 ≤ (6322592772361/50000000000000 : ℝ)^3147
        have hw : |(-2100906703/10000000000 : ℝ)|=(2100906703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s6_7 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272730067/625000000 : ℝ)*x 0 + (2246042237/5000000000 : ℝ)*x 1 + (529868081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272730067/625000000 : ℝ)^4171 ≤ (16658467316091/50000000000000 : ℝ)^3147 := by
    have hnat : (272730067 : ℕ)^4171*50000000000000^3147 ≤ 16658467316091^3147*625000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272730067 625000000 16658467316091 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246042237/5000000000 : ℝ)^4171 ≤ (8655620514233/25000000000000 : ℝ)^3147 := by
    have hnat : (2246042237 : ℕ)^4171*25000000000000^3147 ≤ 8655620514233^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246042237 5000000000 8655620514233 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529868081/1250000000 : ℝ)^4171 ≤ (32060583293541/100000000000000 : ℝ)^3147 := by
    have hnat : (529868081 : ℕ)^4171*100000000000000^3147 ≤ 32060583293541^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529868081 1250000000 32060583293541 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272730067/625000000 : ℝ), (2246042237/5000000000 : ℝ), (529868081/1250000000 : ℝ)] ![(16658467316091/50000000000000 : ℝ), (8655620514233/25000000000000 : ℝ), (32060583293541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272730067/625000000 : ℝ)|^4171 ≤ (16658467316091/50000000000000 : ℝ)^3147
        have hw : |(272730067/625000000 : ℝ)|=(272730067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246042237/5000000000 : ℝ)|^4171 ≤ (8655620514233/25000000000000 : ℝ)^3147
        have hw : |(2246042237/5000000000 : ℝ)|=(2246042237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529868081/1250000000 : ℝ)|^4171 ≤ (32060583293541/100000000000000 : ℝ)^3147
        have hw : |(529868081/1250000000 : ℝ)|=(529868081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1149_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (453/4000 : ℝ) ^ (8341/2048 : ℝ) ≤ (14038814235610297/100000000000000000000 : ℝ) := by
    have hpowers : (453/4000 : ℝ)^8341 ≤ (14038814235610297/100000000000000000000 : ℝ)^2048 := by
      have hnat : (453 : ℕ)^8341*100000000000000000000^2048 ≤ 14038814235610297^2048*4000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        453 4000 14038814235610297 100000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (453/4000 : ℝ)) (X := (14038814235610297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3523/25000 : ℝ) ^ (8341/2048 : ℝ) ≤ (3419597358005667/10000000000000000000 : ℝ) := by
    have hpowers : (3523/25000 : ℝ)^8341 ≤ (3419597358005667/10000000000000000000 : ℝ)^2048 := by
      have hnat : (3523 : ℕ)^8341*10000000000000000000^2048 ≤ 3419597358005667^2048*25000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 25000 3419597358005667 10000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/25000 : ℝ)) (X := (3419597358005667/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014038814235610297/50000000000000000000 : ℝ) ≤ (2000137865707959/2000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (50014038814235610297/50000000000000000000 : ℝ)^2048 ≤ (2000137865707959/2000000000000000 : ℝ)^8341 := by
      have hnat : (50014038814235610297 : ℕ)^2048*2000000000000000^8341 ≤ 2000137865707959^8341*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014038814235610297 50000000000000000000 2000137865707959 2000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000137865707959/2000000000000000 : ℝ)) (X := (50014038814235610297/50000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048234787815666967/100000000000000000000 : ℝ) ≤ (2500296028281593/2500000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (100048234787815666967/100000000000000000000 : ℝ)^2048 ≤ (2500296028281593/2500000000000000 : ℝ)^8341 := by
      have hnat : (100048234787815666967 : ℕ)^2048*2500000000000000^8341 ≤ 2500296028281593^8341*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048234787815666967 100000000000000000000 2500296028281593 2500000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500296028281593/2500000000000000 : ℝ)) (X := (100048234787815666967/100000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003419597358005667/5000000000000000000 : ℝ) ≤ (10001678897712949/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (5003419597358005667/5000000000000000000 : ℝ)^2048 ≤ (10001678897712949/10000000000000000 : ℝ)^8341 := by
      have hnat : (5003419597358005667 : ℕ)^2048*10000000000000000^8341 ≤ 10001678897712949^8341*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003419597358005667 5000000000000000000 10001678897712949 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001678897712949/10000000000000000 : ℝ)) (X := (5003419597358005667/5000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14038814235610297/100000000000000000000 : ℝ) ≤ ((5532140100236728743/5534000000000000000 : ℝ)+2*(494784586577/276700000000000 : ℝ)*(453/4000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (5532140100236728743/5534000000000000000 : ℝ)+2*(494784586577/276700000000000 : ℝ)*(453/4000 : ℝ)=(2000137865707959/2000000000000000 : ℝ) by norm_num, show 1+2*(14038814235610297/100000000000000000000 : ℝ)=(50014038814235610297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3419597358005667/10000000000000000000 : ℝ)+(14038814235610297/100000000000000000000 : ℝ) ≤ ((5532140100236728743/5534000000000000000 : ℝ)+(494784586577/276700000000000 : ℝ)*((3523/25000 : ℝ)+(453/4000 : ℝ)))^(8341/2048 : ℝ) := by
    rw [show (5532140100236728743/5534000000000000000 : ℝ)+(494784586577/276700000000000 : ℝ)*((3523/25000 : ℝ)+(453/4000 : ℝ))=(2500296028281593/2500000000000000 : ℝ) by norm_num, show 1+(3419597358005667/10000000000000000000 : ℝ)+(14038814235610297/100000000000000000000 : ℝ)=(100048234787815666967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3419597358005667/10000000000000000000 : ℝ) ≤ ((5532140100236728743/5534000000000000000 : ℝ)+2*(494784586577/276700000000000 : ℝ)*(3523/25000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (5532140100236728743/5534000000000000000 : ℝ)+2*(494784586577/276700000000000 : ℝ)*(3523/25000 : ℝ)=(10001678897712949/10000000000000000 : ℝ) by norm_num, show 1+2*(3419597358005667/10000000000000000000 : ℝ)=(5003419597358005667/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5532140100236728743/5534000000000000000 : ℝ)*(X 1 0+X 2 0)+(494784586577/276700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (5532140100236728743/5534000000000000000 : ℝ)) (alpha := (494784586577/276700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5532140100236728743/5534000000000000000 : ℝ)*(X 0 1+X 2 1)+(494784586577/276700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (5532140100236728743/5534000000000000000 : ℝ)) (alpha := (494784586577/276700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5532140100236728743/5534000000000000000 : ℝ)*(X 0 2+X 1 2)+(494784586577/276700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (5532140100236728743/5534000000000000000 : ℝ)) (alpha := (494784586577/276700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1081756977/5000000000 : ℝ)*X 0 0+(5393244921/10000000000 : ℝ)*X 0 1+(2632766733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344816789/10000000000 : ℝ)*X 1 0+(-1114147191/5000000000 : ℝ)*X 1 1+(2632766733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344816789/10000000000 : ℝ)*X 2 0+(2632766733/5000000000 : ℝ)*X 2 1+(-1114147191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545458901/1250000000 : ℝ)*X 0 0+(264893727/625000000 : ℝ)*X 0 1+(1123181793/2500000000 : ℝ)*X 0 2+(545458901/1250000000 : ℝ)*X 1 0+(264893727/625000000 : ℝ)*X 1 1+(1123181793/2500000000 : ℝ)*X 1 2+(545458901/1250000000 : ℝ)*X 2 0+(264893727/625000000 : ℝ)*X 2 1+(1123181793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163518931/10000000000 : ℝ)*X 0 0+(526585603/1000000000 : ℝ)*X 0 1+(2696460579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312443837/10000000000 : ℝ)*X 1 0+(-2100906673/10000000000 : ℝ)*X 1 1+(5392921149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062488767/2000000000 : ℝ)*X 2 0+(5392921129/10000000000 : ℝ)*X 2 1+(-2100906703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272730067/625000000 : ℝ)*X 0 0+(2246042237/5000000000 : ℝ)*X 0 1+(529868081/1250000000 : ℝ)*X 0 2+(272730067/625000000 : ℝ)*X 1 0+(2246042237/5000000000 : ℝ)*X 1 1+(529868081/1250000000 : ℝ)*X 1 2+(272730067/625000000 : ℝ)*X 2 0+(2246042237/5000000000 : ℝ)*X 2 1+(529868081/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (318144854258530525417288491/34587500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1812235459/100000000000000 : ℝ)*(base19) + (1686992101/100000000000000 : ℝ)*(base23) + (66940279/100000000000000 : ℝ)*(lower2) + (116047821/50000000000000 : ℝ)*(upper3) + (69705823/50000000000000 : ℝ)*(upper5) + (735043432336679/12500000000000 : ℝ)*(major0) + (735043432336679/12500000000000 : ℝ)*(major1) + (735043432336679/12500000000000 : ℝ)*(major2) + (122346916854787/1562500000000 : ℝ)*(sp0) + (1566050000007597/20000000000000 : ℝ)*(sp1) + (7830250125281343/100000000000000 : ℝ)*(sp2) + (982604030513827/25000000000000 : ℝ)*(sp3) + (12283391769/25000000000000 : ℝ)*(sp4) + (13338224701/50000000000000 : ℝ)*(sp7) + (393044279850471/10000000000000 : ℝ)*(f.failure) + (1957562953068361/25000000000000 : ℝ)*(f.sum) + (837398522009/3458750000000000000000000000 : ℝ)*base66 + (1461597874071975503/69175000000000000000000000000000 : ℝ)*base68 + (1106555703183275503/69175000000000000000000000000000 : ℝ)*base70 + (281635316085849497/69175000000000000000000000000000 : ℝ)*base71 + (34418193604813/6917500000000000000000000000 : ℝ)*base74 + (1301961278739225503/69175000000000000000000000000000 : ℝ)*base76 + (586451267848000503/69175000000000000000000000000000 : ℝ)*base78 + (87818389022774497/69175000000000000000000000000000 : ℝ)*base79 + (40118791299073/6917500000000000000000000000 : ℝ)*base82 + (140731/200000000000000000000 : ℝ)*base89 + (140731/200000000000000000000 : ℝ)*base91 + (140731/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (149319966797015041496673/13835000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1075277973/50000000000000 : ℝ)*(base19) + (2255793849/100000000000000 : ℝ)*(base23) + (108926693/50000000000000 : ℝ)*(upper3) + (11642403/20000000000000 : ℝ)*(lower4) + (253244963/100000000000000 : ℝ)*(upper5) + (5910182387083583/100000000000000 : ℝ)*(major0) + (5910182387083583/100000000000000 : ℝ)*(major1) + (5910182387083583/100000000000000 : ℝ)*(major2) + (60118976617/100000000000000 : ℝ)*(sp1) + (748664691/1250000000000 : ℝ)*(sp2) + (196749496390251/2500000000000 : ℝ)*(sp4) + (7869917586077477/100000000000000 : ℝ)*(sp5) + (491869856665057/6250000000000 : ℝ)*(sp6) + (790076911758663/20000000000000 : ℝ)*(sp7) + (790076911758663/20000000000000 : ℝ)*(f.failure) + (196749496390251/2500000000000 : ℝ)*(f.sum) + (79737643167991/13835000000000000000000000000 : ℝ)*base65 + (4399400802313346169/553400000000000000000000000000000 : ℝ)*base67 + (1909758713748653831/553400000000000000000000000000000 : ℝ)*base70 + (8737512681724546169/553400000000000000000000000000000 : ℝ)*base71 + (16714634700717/6917500000000000000000000000 : ℝ)*base74 + (3258726152533653831/553400000000000000000000000000000 : ℝ)*base76 + (522969601139346169/553400000000000000000000000000000 : ℝ)*base77 + (7400198938441853831/553400000000000000000000000000000 : ℝ)*base80 + (3623095996649/13835000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (435557/400000000000000000000 : ℝ)*base90 + (435557/400000000000000000000 : ℝ)*base92 + (435557/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1149_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1149_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1149_s7_0 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163539543/10000000000 : ℝ)*x 0 + (5392936011/10000000000 : ℝ)*x 1 + (5265825629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163539543/10000000000 : ℝ)^4171 ≤ (6573620376323/50000000000000 : ℝ)^3147 := by
    have hnat : (2163539543 : ℕ)^4171*50000000000000^3147 ≤ 6573620376323^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163539543 10000000000 6573620376323 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392936011/10000000000 : ℝ)^4171 ≤ (5514093202623/12500000000000 : ℝ)^3147 := by
    have hnat : (5392936011 : ℕ)^4171*12500000000000^3147 ≤ 5514093202623^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392936011 10000000000 5514093202623 12500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265825629/10000000000 : ℝ)^4171 ≤ (10685003401341/25000000000000 : ℝ)^3147 := by
    have hnat : (5265825629 : ℕ)^4171*25000000000000^3147 ≤ 10685003401341^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265825629 10000000000 10685003401341 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163539543/10000000000 : ℝ), (5392936011/10000000000 : ℝ), (5265825629/10000000000 : ℝ)] ![(6573620376323/50000000000000 : ℝ), (5514093202623/12500000000000 : ℝ), (10685003401341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163539543/10000000000 : ℝ)|^4171 ≤ (6573620376323/50000000000000 : ℝ)^3147
        have hw : |(-2163539543/10000000000 : ℝ)|=(2163539543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392936011/10000000000 : ℝ)|^4171 ≤ (5514093202623/12500000000000 : ℝ)^3147
        have hw : |(5392936011/10000000000 : ℝ)|=(5392936011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265825629/10000000000 : ℝ)|^4171 ≤ (10685003401341/25000000000000 : ℝ)^3147
        have hw : |(5265825629/10000000000 : ℝ)|=(5265825629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_1 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344739423/10000000000 : ℝ)*x 0 + (-2228010581/10000000000 : ℝ)*x 1 + (5265825733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344739423/10000000000 : ℝ)^4171 ≤ (43590992129187/100000000000000 : ℝ)^3147 := by
    have hnat : (5344739423 : ℕ)^4171*100000000000000^3147 ≤ 43590992129187^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344739423 10000000000 43590992129187 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228010581/10000000000 : ℝ)^4171 ≤ (3417248284227/25000000000000 : ℝ)^3147 := by
    have hnat : (2228010581 : ℕ)^4171*25000000000000^3147 ≤ 3417248284227^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228010581 10000000000 3417248284227 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265825733/10000000000 : ℝ)^4171 ≤ (8548002944829/20000000000000 : ℝ)^3147 := by
    have hnat : (5265825733 : ℕ)^4171*20000000000000^3147 ≤ 8548002944829^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265825733 10000000000 8548002944829 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344739423/10000000000 : ℝ), (-2228010581/10000000000 : ℝ), (5265825733/10000000000 : ℝ)] ![(43590992129187/100000000000000 : ℝ), (3417248284227/25000000000000 : ℝ), (8548002944829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344739423/10000000000 : ℝ)|^4171 ≤ (43590992129187/100000000000000 : ℝ)^3147
        have hw : |(5344739423/10000000000 : ℝ)|=(5344739423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228010581/10000000000 : ℝ)|^4171 ≤ (3417248284227/25000000000000 : ℝ)^3147
        have hw : |(-2228010581/10000000000 : ℝ)|=(2228010581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265825733/10000000000 : ℝ)|^4171 ≤ (8548002944829/20000000000000 : ℝ)^3147
        have hw : |(5265825733/10000000000 : ℝ)|=(5265825733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_2 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344739479/10000000000 : ℝ)*x 0 + (5265825687/10000000000 : ℝ)*x 1 + (-2228010567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344739479/10000000000 : ℝ)^4171 ≤ (4359099273453/10000000000000 : ℝ)^3147 := by
    have hnat : (5344739479 : ℕ)^4171*10000000000000^3147 ≤ 4359099273453^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344739479 10000000000 4359099273453 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265825687/10000000000 : ℝ)^4171 ≤ (427400142293/1000000000000 : ℝ)^3147 := by
    have hnat : (5265825687 : ℕ)^4171*1000000000000^3147 ≤ 427400142293^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265825687 10000000000 427400142293 1000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228010567/10000000000 : ℝ)^4171 ≤ (13668993023069/100000000000000 : ℝ)^3147 := by
    have hnat : (2228010567 : ℕ)^4171*100000000000000^3147 ≤ 13668993023069^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228010567 10000000000 13668993023069 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344739479/10000000000 : ℝ), (5265825687/10000000000 : ℝ), (-2228010567/10000000000 : ℝ)] ![(4359099273453/10000000000000 : ℝ), (427400142293/1000000000000 : ℝ), (13668993023069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344739479/10000000000 : ℝ)|^4171 ≤ (4359099273453/10000000000000 : ℝ)^3147
        have hw : |(5344739479/10000000000 : ℝ)|=(5344739479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265825687/10000000000 : ℝ)|^4171 ≤ (427400142293/1000000000000 : ℝ)^3147
        have hw : |(5265825687/10000000000 : ℝ)|=(5265825687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228010567/10000000000 : ℝ)|^4171 ≤ (13668993023069/100000000000000 : ℝ)^3147
        have hw : |(-2228010567/10000000000 : ℝ)|=(2228010567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_3 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181843299/5000000000 : ℝ)*x 0 + (4238896417/10000000000 : ℝ)*x 1 + (4492126329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181843299/5000000000 : ℝ)^4171 ≤ (3331699055209/10000000000000 : ℝ)^3147 := by
    have hnat : (2181843299 : ℕ)^4171*10000000000000^3147 ≤ 3331699055209^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181843299 5000000000 3331699055209 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238896417/10000000000 : ℝ)^4171 ≤ (3206009980901/10000000000000 : ℝ)^3147 := by
    have hnat : (4238896417 : ℕ)^4171*10000000000000^3147 ≤ 3206009980901^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238896417 10000000000 3206009980901 10000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492126329/10000000000 : ℝ)^4171 ≤ (34622909621527/100000000000000 : ℝ)^3147 := by
    have hnat : (4492126329 : ℕ)^4171*100000000000000^3147 ≤ 34622909621527^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492126329 10000000000 34622909621527 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181843299/5000000000 : ℝ), (4238896417/10000000000 : ℝ), (4492126329/10000000000 : ℝ)] ![(3331699055209/10000000000000 : ℝ), (3206009980901/10000000000000 : ℝ), (34622909621527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181843299/5000000000 : ℝ)|^4171 ≤ (3331699055209/10000000000000 : ℝ)^3147
        have hw : |(2181843299/5000000000 : ℝ)|=(2181843299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238896417/10000000000 : ℝ)|^4171 ≤ (3206009980901/10000000000000 : ℝ)^3147
        have hw : |(4238896417/10000000000 : ℝ)|=(4238896417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492126329/10000000000 : ℝ)|^4171 ≤ (34622909621527/100000000000000 : ℝ)^3147
        have hw : |(4492126329/10000000000 : ℝ)|=(4492126329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_4 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-540886071/2500000000 : ℝ)*x 0 + (5266145313/10000000000 : ℝ)*x 1 + (5392615271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540886071/2500000000 : ℝ)^4171 ≤ (2629455787363/20000000000000 : ℝ)^3147 := by
    have hnat : (540886071 : ℕ)^4171*20000000000000^3147 ≤ 2629455787363^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540886071 2500000000 2629455787363 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266145313/10000000000 : ℝ)^4171 ≤ (42743452642133/100000000000000 : ℝ)^3147 := by
    have hnat : (5266145313 : ℕ)^4171*100000000000000^3147 ≤ 42743452642133^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266145313 10000000000 42743452642133 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392615271/10000000000 : ℝ)^4171 ≤ (5513658551101/12500000000000 : ℝ)^3147 := by
    have hnat : (5392615271 : ℕ)^4171*12500000000000^3147 ≤ 5513658551101^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392615271 10000000000 5513658551101 12500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540886071/2500000000 : ℝ), (5266145313/10000000000 : ℝ), (5392615271/10000000000 : ℝ)] ![(2629455787363/20000000000000 : ℝ), (42743452642133/100000000000000 : ℝ), (5513658551101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540886071/2500000000 : ℝ)|^4171 ≤ (2629455787363/20000000000000 : ℝ)^3147
        have hw : |(-540886071/2500000000 : ℝ)|=(540886071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266145313/10000000000 : ℝ)|^4171 ≤ (42743452642133/100000000000000 : ℝ)^3147
        have hw : |(5266145313/10000000000 : ℝ)|=(5266145313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392615271/10000000000 : ℝ)|^4171 ≤ (5513658551101/12500000000000 : ℝ)^3147
        have hw : |(5392615271/10000000000 : ℝ)|=(5392615271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_5 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312518719/10000000000 : ℝ)*x 0 + (-210122103/1000000000 : ℝ)*x 1 + (539261531/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312518719/10000000000 : ℝ)^4171 ≤ (2162151902047/5000000000000 : ℝ)^3147 := by
    have hnat : (5312518719 : ℕ)^4171*5000000000000^3147 ≤ 2162151902047^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312518719 10000000000 2162151902047 5000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210122103/1000000000 : ℝ)^4171 ≤ (2529538624191/20000000000000 : ℝ)^3147 := by
    have hnat : (210122103 : ℕ)^4171*20000000000000^3147 ≤ 2529538624191^3147*1000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210122103 1000000000 2529538624191 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539261531/1000000000 : ℝ)^4171 ≤ (44109268831611/100000000000000 : ℝ)^3147 := by
    have hnat : (539261531 : ℕ)^4171*100000000000000^3147 ≤ 44109268831611^3147*1000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539261531 1000000000 44109268831611 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312518719/10000000000 : ℝ), (-210122103/1000000000 : ℝ), (539261531/1000000000 : ℝ)] ![(2162151902047/5000000000000 : ℝ), (2529538624191/20000000000000 : ℝ), (44109268831611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312518719/10000000000 : ℝ)|^4171 ≤ (2162151902047/5000000000000 : ℝ)^3147
        have hw : |(5312518719/10000000000 : ℝ)|=(5312518719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210122103/1000000000 : ℝ)|^4171 ≤ (2529538624191/20000000000000 : ℝ)^3147
        have hw : |(-210122103/1000000000 : ℝ)|=(210122103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539261531/1000000000 : ℝ)|^4171 ≤ (44109268831611/100000000000000 : ℝ)^3147
        have hw : |(539261531/1000000000 : ℝ)|=(539261531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_6 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312518721/10000000000 : ℝ)*x 0 + (1348153827/2500000000 : ℝ)*x 1 + (-210122103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312518721/10000000000 : ℝ)^4171 ≤ (43243038062517/100000000000000 : ℝ)^3147 := by
    have hnat : (5312518721 : ℕ)^4171*100000000000000^3147 ≤ 43243038062517^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312518721 10000000000 43243038062517 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348153827/2500000000 : ℝ)^4171 ≤ (44109268809929/100000000000000 : ℝ)^3147 := by
    have hnat : (1348153827 : ℕ)^4171*100000000000000^3147 ≤ 44109268809929^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348153827 2500000000 44109268809929 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210122103/1000000000 : ℝ)^4171 ≤ (2529538624191/20000000000000 : ℝ)^3147 := by
    have hnat : (210122103 : ℕ)^4171*20000000000000^3147 ≤ 2529538624191^3147*1000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210122103 1000000000 2529538624191 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312518721/10000000000 : ℝ), (1348153827/2500000000 : ℝ), (-210122103/1000000000 : ℝ)] ![(43243038062517/100000000000000 : ℝ), (44109268809929/100000000000000 : ℝ), (2529538624191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312518721/10000000000 : ℝ)|^4171 ≤ (43243038062517/100000000000000 : ℝ)^3147
        have hw : |(5312518721/10000000000 : ℝ)|=(5312518721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348153827/2500000000 : ℝ)|^4171 ≤ (44109268809929/100000000000000 : ℝ)^3147
        have hw : |(1348153827/2500000000 : ℝ)|=(1348153827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210122103/1000000000 : ℝ)|^4171 ≤ (2529538624191/20000000000000 : ℝ)^3147
        have hw : |(-210122103/1000000000 : ℝ)|=(210122103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s7_7 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136365507/312500000 : ℝ)*x 0 + (2245744859/5000000000 : ℝ)*x 1 + (4239535413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136365507/312500000 : ℝ)^4171 ≤ (33317087961671/100000000000000 : ℝ)^3147 := by
    have hnat : (136365507 : ℕ)^4171*100000000000000^3147 ≤ 33317087961671^3147*312500000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136365507 312500000 33317087961671 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245744859/5000000000 : ℝ)^4171 ≤ (34616406540389/100000000000000 : ℝ)^3147 := by
    have hnat : (2245744859 : ℕ)^4171*100000000000000^3147 ≤ 34616406540389^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245744859 5000000000 34616406540389 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239535413/10000000000 : ℝ)^4171 ≤ (16033252737601/50000000000000 : ℝ)^3147 := by
    have hnat : (4239535413 : ℕ)^4171*50000000000000^3147 ≤ 16033252737601^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239535413 10000000000 16033252737601 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136365507/312500000 : ℝ), (2245744859/5000000000 : ℝ), (4239535413/10000000000 : ℝ)] ![(33317087961671/100000000000000 : ℝ), (34616406540389/100000000000000 : ℝ), (16033252737601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136365507/312500000 : ℝ)|^4171 ≤ (33317087961671/100000000000000 : ℝ)^3147
        have hw : |(136365507/312500000 : ℝ)|=(136365507/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245744859/5000000000 : ℝ)|^4171 ≤ (34616406540389/100000000000000 : ℝ)^3147
        have hw : |(2245744859/5000000000 : ℝ)|=(2245744859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239535413/10000000000 : ℝ)|^4171 ≤ (16033252737601/50000000000000 : ℝ)^3147
        have hw : |(4239535413/10000000000 : ℝ)|=(4239535413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1149_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5681/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/20000 : ℝ) ^ (8341/2048 : ℝ) ≤ (14190893078922587/100000000000000000000 : ℝ) := by
    have hpowers : (2271/20000 : ℝ)^8341 ≤ (14190893078922587/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2271 : ℕ)^8341*100000000000000000000^2048 ≤ 14190893078922587^2048*20000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 20000 14190893078922587 100000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/20000 : ℝ)) (X := (14190893078922587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (8341/2048 : ℝ) ≤ (16945316636572341/50000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^8341 ≤ (16945316636572341/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14061 : ℕ)^8341*50000000000000000000^2048 ≤ 16945316636572341^2048*100000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 16945316636572341 50000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (16945316636572341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014190893078922587/50000000000000000000 : ℝ) ≤ (10000696795058251/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (50014190893078922587/50000000000000000000 : ℝ)^2048 ≤ (10000696795058251/10000000000000000 : ℝ)^8341 := by
      have hnat : (50014190893078922587 : ℕ)^2048*10000000000000000^8341 ≤ 10000696795058251^8341*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014190893078922587 50000000000000000000 10000696795058251 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000696795058251/10000000000000000 : ℝ)) (X := (50014190893078922587/50000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048081526352067269/100000000000000000000 : ℝ) ≤ (10001180351401379/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (100048081526352067269/100000000000000000000 : ℝ)^2048 ≤ (10001180351401379/10000000000000000 : ℝ)^8341 := by
      have hnat : (100048081526352067269 : ℕ)^2048*10000000000000000^8341 ≤ 10001180351401379^8341*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048081526352067269 100000000000000000000 10001180351401379 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001180351401379/10000000000000000 : ℝ)) (X := (100048081526352067269/100000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016945316636572341/25000000000000000000 : ℝ) ≤ (10001663907744507/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (25016945316636572341/25000000000000000000 : ℝ)^2048 ≤ (10001663907744507/10000000000000000 : ℝ)^8341 := by
      have hnat : (25016945316636572341 : ℕ)^2048*10000000000000000^8341 ≤ 10001663907744507^8341*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016945316636572341 25000000000000000000 10001663907744507 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001663907744507/10000000000000000 : ℝ)) (X := (25016945316636572341/25000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14190893078922587/100000000000000000000 : ℝ) ≤ ((4508483993812531721/4510000000000000000 : ℝ)+2*(60444542891/33825000000000 : ℝ)*(2271/20000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (4508483993812531721/4510000000000000000 : ℝ)+2*(60444542891/33825000000000 : ℝ)*(2271/20000 : ℝ)=(10000696795058251/10000000000000000 : ℝ) by norm_num, show 1+2*(14190893078922587/100000000000000000000 : ℝ)=(50014190893078922587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16945316636572341/50000000000000000000 : ℝ)+(14190893078922587/100000000000000000000 : ℝ) ≤ ((4508483993812531721/4510000000000000000 : ℝ)+(60444542891/33825000000000 : ℝ)*((14061/100000 : ℝ)+(2271/20000 : ℝ)))^(8341/2048 : ℝ) := by
    rw [show (4508483993812531721/4510000000000000000 : ℝ)+(60444542891/33825000000000 : ℝ)*((14061/100000 : ℝ)+(2271/20000 : ℝ))=(10001180351401379/10000000000000000 : ℝ) by norm_num, show 1+(16945316636572341/50000000000000000000 : ℝ)+(14190893078922587/100000000000000000000 : ℝ)=(100048081526352067269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16945316636572341/50000000000000000000 : ℝ) ≤ ((4508483993812531721/4510000000000000000 : ℝ)+2*(60444542891/33825000000000 : ℝ)*(14061/100000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (4508483993812531721/4510000000000000000 : ℝ)+2*(60444542891/33825000000000 : ℝ)*(14061/100000 : ℝ)=(10001663907744507/10000000000000000 : ℝ) by norm_num, show 1+2*(16945316636572341/50000000000000000000 : ℝ)=(25016945316636572341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4508483993812531721/4510000000000000000 : ℝ)*(X 1 0+X 2 0)+(60444542891/33825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (4508483993812531721/4510000000000000000 : ℝ)) (alpha := (60444542891/33825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4508483993812531721/4510000000000000000 : ℝ)*(X 0 1+X 2 1)+(60444542891/33825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (4508483993812531721/4510000000000000000 : ℝ)) (alpha := (60444542891/33825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4508483993812531721/4510000000000000000 : ℝ)*(X 0 2+X 1 2)+(60444542891/33825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (4508483993812531721/4510000000000000000 : ℝ)) (alpha := (60444542891/33825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2163539543/10000000000 : ℝ)*X 0 0+(5392936011/10000000000 : ℝ)*X 0 1+(5265825629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344739423/10000000000 : ℝ)*X 1 0+(-2228010581/10000000000 : ℝ)*X 1 1+(5265825733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344739479/10000000000 : ℝ)*X 2 0+(5265825687/10000000000 : ℝ)*X 2 1+(-2228010567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181843299/5000000000 : ℝ)*X 0 0+(4238896417/10000000000 : ℝ)*X 0 1+(4492126329/10000000000 : ℝ)*X 0 2+(2181843299/5000000000 : ℝ)*X 1 0+(4238896417/10000000000 : ℝ)*X 1 1+(4492126329/10000000000 : ℝ)*X 1 2+(2181843299/5000000000 : ℝ)*X 2 0+(4238896417/10000000000 : ℝ)*X 2 1+(4492126329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-540886071/2500000000 : ℝ)*X 0 0+(5266145313/10000000000 : ℝ)*X 0 1+(5392615271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312518719/10000000000 : ℝ)*X 1 0+(-210122103/1000000000 : ℝ)*X 1 1+(539261531/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312518721/10000000000 : ℝ)*X 2 0+(1348153827/2500000000 : ℝ)*X 2 1+(-210122103/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136365507/312500000 : ℝ)*X 0 0+(2245744859/5000000000 : ℝ)*X 0 1+(4239535413/10000000000 : ℝ)*X 0 2+(136365507/312500000 : ℝ)*X 1 0+(2245744859/5000000000 : ℝ)*X 1 1+(4239535413/10000000000 : ℝ)*X 1 2+(136365507/312500000 : ℝ)*X 2 0+(2245744859/5000000000 : ℝ)*X 2 1+(4239535413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1048301412398075416886759/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4897109/800000000000 : ℝ)*(base19) + (595670079/100000000000000 : ℝ)*(base23) + (204997/195312500000 : ℝ)*(upper3) + (52858433/100000000000000 : ℝ)*(upper4) + (70971121/100000000000000 : ℝ)*(upper5) + (590810892358777/10000000000000 : ℝ)*(major0) + (590810892358777/10000000000000 : ℝ)*(major1) + (590810892358777/10000000000000 : ℝ)*(major2) + (7867198132329233/100000000000000 : ℝ)*(sp0) + (7867218551696497/100000000000000 : ℝ)*(sp1) + (7867218568165043/100000000000000 : ℝ)*(sp2) + (493623595527717/12500000000000 : ℝ)*(sp3) + (21031505889/100000000000000 : ℝ)*(sp4) + (9885027571/100000000000000 : ℝ)*(sp7) + (987249662312327/25000000000000 : ℝ)*(f.failure) + (3933609581917561/50000000000000 : ℝ)*(f.sum) + (1061655175321/270600000000000000000000000 : ℝ)*base66 + (1103695509535595651/135300000000000000000000000000000 : ℝ)*base67 + (93954347339304349/135300000000000000000000000000000 : ℝ)*base70 + (317670896514695651/135300000000000000000000000000000 : ℝ)*base71 + (379111645493/1353000000000000000000000000 : ℝ)*base74 + (3022895762138195651/135300000000000000000000000000000 : ℝ)*base75 + (742116282694895651/135300000000000000000000000000000 : ℝ)*base77 + (1476866206684295651/135300000000000000000000000000000 : ℝ)*base79 + (1956066077701/676500000000000000000000000 : ℝ)*base82 + (454053/500000000000000000000 : ℝ)*base90 + (454053/500000000000000000000 : ℝ)*base92 + (454053/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65648201041930542344347721/10250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1046471219/100000000000000 : ℝ)*(base19) + (236565767/20000000000000 : ℝ)*(base23) + (13926997/10000000000000 : ℝ)*(upper3) + (11494011/20000000000000 : ℝ)*(lower4) + (28417761/25000000000000 : ℝ)*(upper5) + (5937993690685337/100000000000000 : ℝ)*(major0) + (5937993690685337/100000000000000 : ℝ)*(major1) + (5937993690685337/100000000000000 : ℝ)*(major2) + (14737683461/50000000000000 : ℝ)*(sp1) + (6726129029/20000000000000 : ℝ)*(sp2) + (158140268919867/2000000000000 : ℝ)*(sp4) + (7906982924155209/100000000000000 : ℝ)*(sp5) + (790697863251937/10000000000000 : ℝ)*(sp6) + (396897372188723/10000000000000 : ℝ)*(sp7) + (396897372188723/10000000000000 : ℝ)*(f.failure) + (158140268919867/2000000000000 : ℝ)*(f.sum) + (1359797681317/1691250000000000000000000000 : ℝ)*base65 + (12320461056236975069/1353000000000000000000000000000000 : ℝ)*base68 + (27502276721186975069/1353000000000000000000000000000000 : ℝ)*base70 + (16605510970007975069/1353000000000000000000000000000000 : ℝ)*base72 + (1489176598453/422812500000000000000000000 : ℝ)*base73 + (18545153922584975069/1353000000000000000000000000000000 : ℝ)*base76 + (6815043245651975069/1353000000000000000000000000000000 : ℝ)*base78 + (4646582398938024931/1353000000000000000000000000000000 : ℝ)*base79 + (19283292685693/6765000000000000000000000000 : ℝ)*base81 + (881897/200000000000000000000 : ℝ)*base90 + (881897/200000000000000000000 : ℝ)*base92 + (881897/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1149_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1149_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1149_s8_0 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16902691/78125000 : ℝ)*x 0 + (168527071/312500000 : ℝ)*x 1 + (5265892239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16902691/78125000 : ℝ)^4171 ≤ (13147280257677/100000000000000 : ℝ)^3147 := by
    have hnat : (16902691 : ℕ)^4171*100000000000000^3147 ≤ 13147280257677^3147*78125000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16902691 78125000 13147280257677 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168527071/312500000 : ℝ)^4171 ≤ (1764479582383/4000000000000 : ℝ)^3147 := by
    have hnat : (168527071 : ℕ)^4171*4000000000000^3147 ≤ 1764479582383^3147*312500000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168527071 312500000 1764479582383 4000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265892239/10000000000 : ℝ)^4171 ≤ (42740730164367/100000000000000 : ℝ)^3147 := by
    have hnat : (5265892239 : ℕ)^4171*100000000000000^3147 ≤ 42740730164367^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265892239 10000000000 42740730164367 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16902691/78125000 : ℝ), (168527071/312500000 : ℝ), (5265892239/10000000000 : ℝ)] ![(13147280257677/100000000000000 : ℝ), (1764479582383/4000000000000 : ℝ), (42740730164367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16902691/78125000 : ℝ)|^4171 ≤ (13147280257677/100000000000000 : ℝ)^3147
        have hw : |(-16902691/78125000 : ℝ)|=(16902691/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168527071/312500000 : ℝ)|^4171 ≤ (1764479582383/4000000000000 : ℝ)^3147
        have hw : |(168527071/312500000 : ℝ)|=(168527071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265892239/10000000000 : ℝ)|^4171 ≤ (42740730164367/100000000000000 : ℝ)^3147
        have hw : |(5265892239/10000000000 : ℝ)|=(5265892239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_1 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267236109/500000000 : ℝ)*x 0 + (-2227945527/10000000000 : ℝ)*x 1 + (658236529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267236109/500000000 : ℝ)^4171 ≤ (43590805737617/100000000000000 : ℝ)^3147 := by
    have hnat : (267236109 : ℕ)^4171*100000000000000^3147 ≤ 43590805737617^3147*500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267236109 500000000 43590805737617 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227945527/10000000000 : ℝ)^4171 ≤ (2733692832499/20000000000000 : ℝ)^3147 := by
    have hnat : (2227945527 : ℕ)^4171*20000000000000^3147 ≤ 2733692832499^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227945527 10000000000 2733692832499 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658236529/1250000000 : ℝ)^4171 ≤ (5342591261133/12500000000000 : ℝ)^3147 := by
    have hnat : (658236529 : ℕ)^4171*12500000000000^3147 ≤ 5342591261133^3147*1250000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658236529 1250000000 5342591261133 12500000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267236109/500000000 : ℝ), (-2227945527/10000000000 : ℝ), (658236529/1250000000 : ℝ)] ![(43590805737617/100000000000000 : ℝ), (2733692832499/20000000000000 : ℝ), (5342591261133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267236109/500000000 : ℝ)|^4171 ≤ (43590805737617/100000000000000 : ℝ)^3147
        have hw : |(267236109/500000000 : ℝ)|=(267236109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227945527/10000000000 : ℝ)|^4171 ≤ (2733692832499/20000000000000 : ℝ)^3147
        have hw : |(-2227945527/10000000000 : ℝ)|=(2227945527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658236529/1250000000 : ℝ)|^4171 ≤ (5342591261133/12500000000000 : ℝ)^3147
        have hw : |(658236529/1250000000 : ℝ)|=(658236529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_2 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672361089/5000000000 : ℝ)*x 0 + (2632946117/5000000000 : ℝ)*x 1 + (-1113972763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672361089/5000000000 : ℝ)^4171 ≤ (21795402857999/50000000000000 : ℝ)^3147 := by
    have hnat : (2672361089 : ℕ)^4171*50000000000000^3147 ≤ 21795402857999^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672361089 5000000000 21795402857999 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632946117/5000000000 : ℝ)^4171 ≤ (42740730110579/100000000000000 : ℝ)^3147 := by
    have hnat : (2632946117 : ℕ)^4171*100000000000000^3147 ≤ 42740730110579^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632946117 5000000000 42740730110579 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113972763/5000000000 : ℝ)^4171 ≤ (13668464154363/100000000000000 : ℝ)^3147 := by
    have hnat : (1113972763 : ℕ)^4171*100000000000000^3147 ≤ 13668464154363^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113972763 5000000000 13668464154363 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672361089/5000000000 : ℝ), (2632946117/5000000000 : ℝ), (-1113972763/5000000000 : ℝ)] ![(21795402857999/50000000000000 : ℝ), (42740730110579/100000000000000 : ℝ), (13668464154363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672361089/5000000000 : ℝ)|^4171 ≤ (21795402857999/50000000000000 : ℝ)^3147
        have hw : |(2672361089/5000000000 : ℝ)|=(2672361089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632946117/5000000000 : ℝ)|^4171 ≤ (42740730110579/100000000000000 : ℝ)^3147
        have hw : |(2632946117/5000000000 : ℝ)|=(2632946117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113972763/5000000000 : ℝ)|^4171 ≤ (13668464154363/100000000000000 : ℝ)^3147
        have hw : |(-1113972763/5000000000 : ℝ)|=(1113972763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_3 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181844979/5000000000 : ℝ)*x 0 + (2119515877/5000000000 : ℝ)*x 1 + (4491990193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181844979/5000000000 : ℝ)^4171 ≤ (33317024553349/100000000000000 : ℝ)^3147 := by
    have hnat : (2181844979 : ℕ)^4171*100000000000000^3147 ≤ 33317024553349^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181844979 5000000000 33317024553349 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119515877/5000000000 : ℝ)^4171 ≤ (32061456479299/100000000000000 : ℝ)^3147 := by
    have hnat : (2119515877 : ℕ)^4171*100000000000000^3147 ≤ 32061456479299^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119515877 5000000000 32061456479299 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491990193/10000000000 : ℝ)^4171 ≤ (17310759472871/50000000000000 : ℝ)^3147 := by
    have hnat : (4491990193 : ℕ)^4171*50000000000000^3147 ≤ 17310759472871^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491990193 10000000000 17310759472871 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181844979/5000000000 : ℝ), (2119515877/5000000000 : ℝ), (4491990193/10000000000 : ℝ)] ![(33317024553349/100000000000000 : ℝ), (32061456479299/100000000000000 : ℝ), (17310759472871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181844979/5000000000 : ℝ)|^4171 ≤ (33317024553349/100000000000000 : ℝ)^3147
        have hw : |(2181844979/5000000000 : ℝ)|=(2181844979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119515877/5000000000 : ℝ)|^4171 ≤ (32061456479299/100000000000000 : ℝ)^3147
        have hw : |(2119515877/5000000000 : ℝ)|=(2119515877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491990193/10000000000 : ℝ)|^4171 ≤ (17310759472871/50000000000000 : ℝ)^3147
        have hw : |(4491990193/10000000000 : ℝ)|=(4491990193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_4 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163549313/10000000000 : ℝ)*x 0 + (82284549/156250000 : ℝ)*x 1 + (5392546217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163549313/10000000000 : ℝ)^4171 ≤ (6573659720287/50000000000000 : ℝ)^3147 := by
    have hnat : (2163549313 : ℕ)^4171*50000000000000^3147 ≤ 6573659720287^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163549313 10000000000 6573659720287 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82284549/156250000 : ℝ)^4171 ≤ (42744160748931/100000000000000 : ℝ)^3147 := by
    have hnat : (82284549 : ℕ)^4171*100000000000000^3147 ≤ 42744160748931^3147*156250000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82284549 156250000 42744160748931 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392546217/10000000000 : ℝ)^4171 ≤ (22054259894081/50000000000000 : ℝ)^3147 := by
    have hnat : (5392546217 : ℕ)^4171*50000000000000^3147 ≤ 22054259894081^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392546217 10000000000 22054259894081 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163549313/10000000000 : ℝ), (82284549/156250000 : ℝ), (5392546217/10000000000 : ℝ)] ![(6573659720287/50000000000000 : ℝ), (42744160748931/100000000000000 : ℝ), (22054259894081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163549313/10000000000 : ℝ)|^4171 ≤ (6573659720287/50000000000000 : ℝ)^3147
        have hw : |(-2163549313/10000000000 : ℝ)|=(2163549313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82284549/156250000 : ℝ)|^4171 ≤ (42744160748931/100000000000000 : ℝ)^3147
        have hw : |(82284549/156250000 : ℝ)|=(82284549/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392546217/10000000000 : ℝ)|^4171 ≤ (22054259894081/50000000000000 : ℝ)^3147
        have hw : |(5392546217/10000000000 : ℝ)|=(5392546217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_5 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656267999/5000000000 : ℝ)*x 0 + (-2101291553/10000000000 : ℝ)*x 1 + (5392546217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656267999/5000000000 : ℝ)^4171 ≤ (43243224454717/100000000000000 : ℝ)^3147 := by
    have hnat : (2656267999 : ℕ)^4171*100000000000000^3147 ≤ 43243224454717^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656267999 5000000000 43243224454717 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101291553/10000000000 : ℝ)^4171 ≤ (2529651148453/20000000000000 : ℝ)^3147 := by
    have hnat : (2101291553 : ℕ)^4171*20000000000000^3147 ≤ 2529651148453^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101291553 10000000000 2529651148453 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392546217/10000000000 : ℝ)^4171 ≤ (22054259894081/50000000000000 : ℝ)^3147 := by
    have hnat : (5392546217 : ℕ)^4171*50000000000000^3147 ≤ 22054259894081^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392546217 10000000000 22054259894081 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656267999/5000000000 : ℝ), (-2101291553/10000000000 : ℝ), (5392546217/10000000000 : ℝ)] ![(43243224454717/100000000000000 : ℝ), (2529651148453/20000000000000 : ℝ), (22054259894081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656267999/5000000000 : ℝ)|^4171 ≤ (43243224454717/100000000000000 : ℝ)^3147
        have hw : |(2656267999/5000000000 : ℝ)|=(2656267999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101291553/10000000000 : ℝ)|^4171 ≤ (2529651148453/20000000000000 : ℝ)^3147
        have hw : |(-2101291553/10000000000 : ℝ)|=(2101291553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392546217/10000000000 : ℝ)|^4171 ≤ (22054259894081/50000000000000 : ℝ)^3147
        have hw : |(5392546217/10000000000 : ℝ)|=(5392546217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_6 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656267999/5000000000 : ℝ)*x 0 + (5392546217/10000000000 : ℝ)*x 1 + (-2101291553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656267999/5000000000 : ℝ)^4171 ≤ (43243224454717/100000000000000 : ℝ)^3147 := by
    have hnat : (2656267999 : ℕ)^4171*100000000000000^3147 ≤ 43243224454717^3147*5000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656267999 5000000000 43243224454717 100000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392546217/10000000000 : ℝ)^4171 ≤ (22054259894081/50000000000000 : ℝ)^3147 := by
    have hnat : (5392546217 : ℕ)^4171*50000000000000^3147 ≤ 22054259894081^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392546217 10000000000 22054259894081 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101291553/10000000000 : ℝ)^4171 ≤ (2529651148453/20000000000000 : ℝ)^3147 := by
    have hnat : (2101291553 : ℕ)^4171*20000000000000^3147 ≤ 2529651148453^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101291553 10000000000 2529651148453 20000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656267999/5000000000 : ℝ), (5392546217/10000000000 : ℝ), (-2101291553/10000000000 : ℝ)] ![(43243224454717/100000000000000 : ℝ), (22054259894081/50000000000000 : ℝ), (2529651148453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656267999/5000000000 : ℝ)|^4171 ≤ (43243224454717/100000000000000 : ℝ)^3147
        have hw : |(2656267999/5000000000 : ℝ)|=(2656267999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392546217/10000000000 : ℝ)|^4171 ≤ (22054259894081/50000000000000 : ℝ)^3147
        have hw : |(5392546217/10000000000 : ℝ)|=(5392546217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101291553/10000000000 : ℝ)|^4171 ≤ (2529651148453/20000000000000 : ℝ)^3147
        have hw : |(-2101291553/10000000000 : ℝ)|=(2101291553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1149_s8_7 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363699647/10000000000 : ℝ)*x 0 + (1122838719/2500000000 : ℝ)*x 1 + (4239669357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363699647/10000000000 : ℝ)^4171 ≤ (16658561300239/50000000000000 : ℝ)^3147 := by
    have hnat : (4363699647 : ℕ)^4171*50000000000000^3147 ≤ 16658561300239^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363699647 10000000000 16658561300239 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122838719/2500000000 : ℝ)^4171 ≤ (8653757286679/25000000000000 : ℝ)^3147 := by
    have hnat : (1122838719 : ℕ)^4171*25000000000000^3147 ≤ 8653757286679^3147*2500000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122838719 2500000000 8653757286679 25000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239669357/10000000000 : ℝ)^4171 ≤ (16033924123653/50000000000000 : ℝ)^3147 := by
    have hnat : (4239669357 : ℕ)^4171*50000000000000^3147 ≤ 16033924123653^3147*10000000000^4171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239669357 10000000000 16033924123653 50000000000000 4171 3147 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4171/1024 : ℝ)) 4171 3147 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363699647/10000000000 : ℝ), (1122838719/2500000000 : ℝ), (4239669357/10000000000 : ℝ)] ![(16658561300239/50000000000000 : ℝ), (8653757286679/25000000000000 : ℝ), (16033924123653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363699647/10000000000 : ℝ)|^4171 ≤ (16658561300239/50000000000000 : ℝ)^3147
        have hw : |(4363699647/10000000000 : ℝ)|=(4363699647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122838719/2500000000 : ℝ)|^4171 ≤ (8653757286679/25000000000000 : ℝ)^3147
        have hw : |(1122838719/2500000000 : ℝ)|=(1122838719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239669357/10000000000 : ℝ)|^4171 ≤ (16033924123653/50000000000000 : ℝ)^3147
        have hw : |(4239669357/10000000000 : ℝ)|=(4239669357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1149_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5681/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5681/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5681/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5681/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5681/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5681/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5681/50000 : ℝ) ^ (8341/2048 : ℝ) ≤ (2845311252532313/20000000000000000000 : ℝ) := by
    have hpowers : (5681/50000 : ℝ)^8341 ≤ (2845311252532313/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5681 : ℕ)^8341*20000000000000000000^2048 ≤ 2845311252532313^2048*50000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5681 50000 2845311252532313 20000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5681/50000 : ℝ)) (X := (2845311252532313/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (8341/2048 : ℝ) ≤ (33821971107176981/100000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^8341 ≤ (33821971107176981/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7027 : ℕ)^8341*100000000000000000000^2048 ≤ 33821971107176981^2048*50000^8341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 33821971107176981 100000000000000000000 8341 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (33821971107176981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002845311252532313/10000000000000000000 : ℝ) ≤ (10000698545988471/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (10002845311252532313/10000000000000000000 : ℝ)^2048 ≤ (10000698545988471/10000000000000000 : ℝ)^8341 := by
      have hnat : (10002845311252532313 : ℕ)^2048*10000000000000000^8341 ≤ 10000698545988471^8341*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002845311252532313 10000000000000000000 10000698545988471 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000698545988471/10000000000000000 : ℝ)) (X := (10002845311252532313/10000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024024263684919273/50000000000000000000 : ℝ) ≤ (10001179541457507/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (50024024263684919273/50000000000000000000 : ℝ)^2048 ≤ (10001179541457507/10000000000000000 : ℝ)^8341 := by
      have hnat : (50024024263684919273 : ℕ)^2048*10000000000000000^8341 ≤ 10001179541457507^8341*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024024263684919273 50000000000000000000 10001179541457507 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001179541457507/10000000000000000 : ℝ)) (X := (50024024263684919273/50000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033821971107176981/50000000000000000000 : ℝ) ≤ (10001660536926543/10000000000000000 : ℝ) ^ (8341/2048 : ℝ) := by
    have hpowers : (50033821971107176981/50000000000000000000 : ℝ)^2048 ≤ (10001660536926543/10000000000000000 : ℝ)^8341 := by
      have hnat : (50033821971107176981 : ℕ)^2048*10000000000000000^8341 ≤ 10001660536926543^8341*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033821971107176981 50000000000000000000 10001660536926543 10000000000000000 2048 8341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001660536926543/10000000000000000 : ℝ)) (X := (50033821971107176981/50000000000000000000 : ℝ)) (by norm_num) 8341 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2845311252532313/20000000000000000000 : ℝ) ≤ ((6727737586190647467/6730000000000000000 : ℝ)+2*(120248867259/67300000000000 : ℝ)*(5681/50000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (6727737586190647467/6730000000000000000 : ℝ)+2*(120248867259/67300000000000 : ℝ)*(5681/50000 : ℝ)=(10000698545988471/10000000000000000 : ℝ) by norm_num, show 1+2*(2845311252532313/20000000000000000000 : ℝ)=(10002845311252532313/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33821971107176981/100000000000000000000 : ℝ)+(2845311252532313/20000000000000000000 : ℝ) ≤ ((6727737586190647467/6730000000000000000 : ℝ)+(120248867259/67300000000000 : ℝ)*((7027/50000 : ℝ)+(5681/50000 : ℝ)))^(8341/2048 : ℝ) := by
    rw [show (6727737586190647467/6730000000000000000 : ℝ)+(120248867259/67300000000000 : ℝ)*((7027/50000 : ℝ)+(5681/50000 : ℝ))=(10001179541457507/10000000000000000 : ℝ) by norm_num, show 1+(33821971107176981/100000000000000000000 : ℝ)+(2845311252532313/20000000000000000000 : ℝ)=(50024024263684919273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33821971107176981/100000000000000000000 : ℝ) ≤ ((6727737586190647467/6730000000000000000 : ℝ)+2*(120248867259/67300000000000 : ℝ)*(7027/50000 : ℝ))^(8341/2048 : ℝ) := by
    rw [show (6727737586190647467/6730000000000000000 : ℝ)+2*(120248867259/67300000000000 : ℝ)*(7027/50000 : ℝ)=(10001660536926543/10000000000000000 : ℝ) by norm_num, show 1+2*(33821971107176981/100000000000000000000 : ℝ)=(50033821971107176981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6727737586190647467/6730000000000000000 : ℝ)*(X 1 0+X 2 0)+(120248867259/67300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (6727737586190647467/6730000000000000000 : ℝ)) (alpha := (120248867259/67300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6727737586190647467/6730000000000000000 : ℝ)*(X 0 1+X 2 1)+(120248867259/67300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (6727737586190647467/6730000000000000000 : ℝ)) (alpha := (120248867259/67300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6727737586190647467/6730000000000000000 : ℝ)*(X 0 2+X 1 2)+(120248867259/67300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8341/2048 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (6727737586190647467/6730000000000000000 : ℝ)) (alpha := (120248867259/67300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16902691/78125000 : ℝ)*X 0 0+(168527071/312500000 : ℝ)*X 0 1+(5265892239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267236109/500000000 : ℝ)*X 1 0+(-2227945527/10000000000 : ℝ)*X 1 1+(658236529/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672361089/5000000000 : ℝ)*X 2 0+(2632946117/5000000000 : ℝ)*X 2 1+(-1113972763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181844979/5000000000 : ℝ)*X 0 0+(2119515877/5000000000 : ℝ)*X 0 1+(4491990193/10000000000 : ℝ)*X 0 2+(2181844979/5000000000 : ℝ)*X 1 0+(2119515877/5000000000 : ℝ)*X 1 1+(4491990193/10000000000 : ℝ)*X 1 2+(2181844979/5000000000 : ℝ)*X 2 0+(2119515877/5000000000 : ℝ)*X 2 1+(4491990193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163549313/10000000000 : ℝ)*X 0 0+(82284549/156250000 : ℝ)*X 0 1+(5392546217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656267999/5000000000 : ℝ)*X 1 0+(-2101291553/10000000000 : ℝ)*X 1 1+(5392546217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656267999/5000000000 : ℝ)*X 2 0+(5392546217/10000000000 : ℝ)*X 2 1+(-2101291553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363699647/10000000000 : ℝ)*X 0 0+(1122838719/2500000000 : ℝ)*X 0 1+(4239669357/10000000000 : ℝ)*X 0 2+(4363699647/10000000000 : ℝ)*X 1 0+(1122838719/2500000000 : ℝ)*X 1 1+(4239669357/10000000000 : ℝ)*X 1 2+(4363699647/10000000000 : ℝ)*X 2 0+(1122838719/2500000000 : ℝ)*X 2 1+(4239669357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1149_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (976424987767869370354503999/168250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145143977/12500000000000 : ℝ)*(base19) + (1076005131/100000000000000 : ℝ)*(base23) + (43933401/100000000000000 : ℝ)*(lower2) + (71476097/50000000000000 : ℝ)*(upper3) + (82536167/100000000000000 : ℝ)*(upper5) + (5914471162813601/100000000000000 : ℝ)*(major0) + (5914471162813601/100000000000000 : ℝ)*(major1) + (5914471162813601/100000000000000 : ℝ)*(major2) + (1968914815601617/25000000000000 : ℝ)*(sp0) + (7875689781002409/100000000000000 : ℝ)*(sp1) + (3937844933074547/50000000000000 : ℝ)*(sp2) + (494154250620497/12500000000000 : ℝ)*(sp3) + (7919936939/25000000000000 : ℝ)*(sp4) + (8592530869/50000000000000 : ℝ)*(sp7) + (1976625595012857/50000000000000 : ℝ)*(f.failure) + (315027637686169/4000000000000 : ℝ)*(f.sum) + (25645052860071/3365000000000000000000000000 : ℝ)*base66 + (5723316805397698667/673000000000000000000000000000000 : ℝ)*base67 + (11470195555915698667/673000000000000000000000000000000 : ℝ)*base69 + (6987233497132301333/673000000000000000000000000000000 : ℝ)*base72 + (2369311793887/1682500000000000000000000000 : ℝ)*base73 + (21370196508683698667/673000000000000000000000000000000 : ℝ)*base75 + (2340092152491698667/673000000000000000000000000000000 : ℝ)*base77 + (8125470589465698667/673000000000000000000000000000000 : ℝ)*base79 + (18567846062691/3365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (7061723/1000000000000000000000 : ℝ)*base90 + (7061723/1000000000000000000000 : ℝ)*base92 + (7061723/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (445222864960952890030006629/42062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241440031/12500000000000 : ℝ)*(base19) + (2101185351/100000000000000 : ℝ)*(base23) + (677631953/100000000000000 : ℝ)*(lower1) + (212307067/100000000000000 : ℝ)*(upper3) + (15440083/20000000000000 : ℝ)*(lower4) + (43218759/20000000000000 : ℝ)*(upper5) + (743036703652029/12500000000000 : ℝ)*(major0) + (743036703652029/12500000000000 : ℝ)*(major1) + (743036703652029/12500000000000 : ℝ)*(major2) + (4018742739/100000000000000 : ℝ)*(sp2) + (1583080456984691/20000000000000 : ℝ)*(sp4) + (7915400353403207/100000000000000 : ℝ)*(sp5) + (3957698082497683/50000000000000 : ℝ)*(sp6) + (1986592310341267/50000000000000 : ℝ)*(sp7) + (1986592310341267/50000000000000 : ℝ)*(f.failure) + (1583080456984691/20000000000000 : ℝ)*(f.sum) + (10834798283793/3365000000000000000000000000 : ℝ)*base65 + (3502635142720360543/84125000000000000000000000000000 : ℝ)*base67 + (876407582799264457/84125000000000000000000000000000 : ℝ)*base70 + (13150604952387860543/84125000000000000000000000000000 : ℝ)*base71 + (4861904530157/3365000000000000000000000000 : ℝ)*base74 + (7067056817528264457/84125000000000000000000000000000 : ℝ)*base76 + (746155662081139457/84125000000000000000000000000000 : ℝ)*base78 + (1953815365650139457/84125000000000000000000000000000 : ℝ)*base80 + (1771759218451/1682500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1991287/1000000000000000000000 : ℝ)*base89 + (1991287/1000000000000000000000 : ℝ)*base91 + (1991287/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1149_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1149_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1149_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1149_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1149_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1149_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1149_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

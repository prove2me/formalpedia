-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:03:55.967298+00:00
-- url     : https://prove2.me/submissions/af0e88fd-5836-40d1-8a69-4b6c11eb0163

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
theorem support_rectangle_w1062_s0_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917389023/10000000000 : ℝ)*x 0 + (6073006949/10000000000 : ℝ)*x 1 + (1192567989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917389023/10000000000 : ℝ)^8255 ≤ (11118352498397/100000000000000 : ℝ)^6207 := by
    have hnat : (1917389023 : ℕ)^8255*100000000000000^6207 ≤ 11118352498397^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917389023 10000000000 11118352498397 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6073006949/10000000000 : ℝ)^8255 ≤ (51515490872839/100000000000000 : ℝ)^6207 := by
    have hnat : (6073006949 : ℕ)^8255*100000000000000^6207 ≤ 51515490872839^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6073006949 10000000000 51515490872839 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192567989/2500000000 : ℝ)^8255 ≤ (9341539153841/25000000000000 : ℝ)^6207 := by
    have hnat : (1192567989 : ℕ)^8255*25000000000000^6207 ≤ 9341539153841^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192567989 2500000000 9341539153841 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917389023/10000000000 : ℝ), (6073006949/10000000000 : ℝ), (1192567989/2500000000 : ℝ)] ![(11118352498397/100000000000000 : ℝ), (51515490872839/100000000000000 : ℝ), (9341539153841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917389023/10000000000 : ℝ)|^8255 ≤ (11118352498397/100000000000000 : ℝ)^6207
        have hw : |(-1917389023/10000000000 : ℝ)|=(1917389023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6073006949/10000000000 : ℝ)|^8255 ≤ (51515490872839/100000000000000 : ℝ)^6207
        have hw : |(6073006949/10000000000 : ℝ)|=(6073006949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192567989/2500000000 : ℝ)|^8255 ≤ (9341539153841/25000000000000 : ℝ)^6207
        have hw : |(1192567989/2500000000 : ℝ)|=(1192567989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1104260231/2000000000 : ℝ)*x 0 + (-266737089/1000000000 : ℝ)*x 1 + (4770268881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104260231/2000000000 : ℝ)^8255 ≤ (9077327173461/20000000000000 : ℝ)^6207 := by
    have hnat : (1104260231 : ℕ)^8255*20000000000000^6207 ≤ 9077327173461^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104260231 2000000000 9077327173461 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266737089/1000000000 : ℝ)^8255 ≤ (8623619769123/50000000000000 : ℝ)^6207 := by
    have hnat : (266737089 : ℕ)^8255*50000000000000^6207 ≤ 8623619769123^6207*1000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266737089 1000000000 8623619769123 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770268881/10000000000 : ℝ)^8255 ≤ (3736612458103/10000000000000 : ℝ)^6207 := by
    have hnat : (4770268881 : ℕ)^8255*10000000000000^6207 ≤ 3736612458103^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770268881 10000000000 3736612458103 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104260231/2000000000 : ℝ), (-266737089/1000000000 : ℝ), (4770268881/10000000000 : ℝ)] ![(9077327173461/20000000000000 : ℝ), (8623619769123/50000000000000 : ℝ), (3736612458103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104260231/2000000000 : ℝ)|^8255 ≤ (9077327173461/20000000000000 : ℝ)^6207
        have hw : |(1104260231/2000000000 : ℝ)|=(1104260231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266737089/1000000000 : ℝ)|^8255 ≤ (8623619769123/50000000000000 : ℝ)^6207
        have hw : |(-266737089/1000000000 : ℝ)|=(266737089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770268881/10000000000 : ℝ)|^8255 ≤ (3736612458103/10000000000000 : ℝ)^6207
        have hw : |(4770268881/10000000000 : ℝ)|=(4770268881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1380324271/2500000000 : ℝ)*x 0 + (4770272021/10000000000 : ℝ)*x 1 + (-2667372261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380324271/2500000000 : ℝ)^8255 ≤ (5673323920107/12500000000000 : ℝ)^6207 := by
    have hnat : (1380324271 : ℕ)^8255*12500000000000^6207 ≤ 5673323920107^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380324271 2500000000 5673323920107 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4770272021/10000000000 : ℝ)^8255 ≤ (1167692415391/3125000000000 : ℝ)^6207 := by
    have hnat : (4770272021 : ℕ)^8255*3125000000000^6207 ≤ 1167692415391^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770272021 10000000000 1167692415391 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2667372261/10000000000 : ℝ)^8255 ≤ (4311812832029/25000000000000 : ℝ)^6207 := by
    have hnat : (2667372261 : ℕ)^8255*25000000000000^6207 ≤ 4311812832029^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667372261 10000000000 4311812832029 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380324271/2500000000 : ℝ), (4770272021/10000000000 : ℝ), (-2667372261/10000000000 : ℝ)] ![(5673323920107/12500000000000 : ℝ), (1167692415391/3125000000000 : ℝ), (4311812832029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380324271/2500000000 : ℝ)|^8255 ≤ (5673323920107/12500000000000 : ℝ)^6207
        have hw : |(1380324271/2500000000 : ℝ)|=(1380324271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4770272021/10000000000 : ℝ)|^8255 ≤ (1167692415391/3125000000000 : ℝ)^6207
        have hw : |(4770272021/10000000000 : ℝ)|=(4770272021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2667372261/10000000000 : ℝ)|^8255 ≤ (4311812832029/25000000000000 : ℝ)^6207
        have hw : |(-2667372261/10000000000 : ℝ)|=(2667372261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33660339/80000000 : ℝ)*x 0 + (1562541493/5000000000 : ℝ)*x 1 + (2838113531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33660339/80000000 : ℝ)^8255 ≤ (15810539326423/50000000000000 : ℝ)^6207 := by
    have hnat : (33660339 : ℕ)^8255*50000000000000^6207 ≤ 15810539326423^6207*80000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33660339 80000000 15810539326423 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562541493/5000000000 : ℝ)^8255 ≤ (10645378319807/50000000000000 : ℝ)^6207 := by
    have hnat : (1562541493 : ℕ)^8255*50000000000000^6207 ≤ 10645378319807^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562541493 5000000000 10645378319807 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2838113531/5000000000 : ℝ)^8255 ≤ (47088164702621/100000000000000 : ℝ)^6207 := by
    have hnat : (2838113531 : ℕ)^8255*100000000000000^6207 ≤ 47088164702621^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838113531 5000000000 47088164702621 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33660339/80000000 : ℝ), (1562541493/5000000000 : ℝ), (2838113531/5000000000 : ℝ)] ![(15810539326423/50000000000000 : ℝ), (10645378319807/50000000000000 : ℝ), (47088164702621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33660339/80000000 : ℝ)|^8255 ≤ (15810539326423/50000000000000 : ℝ)^6207
        have hw : |(33660339/80000000 : ℝ)|=(33660339/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562541493/5000000000 : ℝ)|^8255 ≤ (10645378319807/50000000000000 : ℝ)^6207
        have hw : |(1562541493/5000000000 : ℝ)|=(1562541493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2838113531/5000000000 : ℝ)|^8255 ≤ (47088164702621/100000000000000 : ℝ)^6207
        have hw : |(2838113531/5000000000 : ℝ)|=(2838113531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922776369/10000000000 : ℝ)*x 0 + (1200977657/2500000000 : ℝ)*x 1 + (6038190689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922776369/10000000000 : ℝ)^8255 ≤ (11159918815003/100000000000000 : ℝ)^6207 := by
    have hnat : (1922776369 : ℕ)^8255*100000000000000^6207 ≤ 11159918815003^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922776369 10000000000 11159918815003 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200977657/2500000000 : ℝ)^8255 ≤ (37717000264513/100000000000000 : ℝ)^6207 := by
    have hnat : (1200977657 : ℕ)^8255*100000000000000^6207 ≤ 37717000264513^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200977657 2500000000 37717000264513 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6038190689/10000000000 : ℝ)^8255 ≤ (6390385112259/12500000000000 : ℝ)^6207 := by
    have hnat : (6038190689 : ℕ)^8255*12500000000000^6207 ≤ 6390385112259^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038190689 10000000000 6390385112259 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922776369/10000000000 : ℝ), (1200977657/2500000000 : ℝ), (6038190689/10000000000 : ℝ)] ![(11159918815003/100000000000000 : ℝ), (37717000264513/100000000000000 : ℝ), (6390385112259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922776369/10000000000 : ℝ)|^8255 ≤ (11159918815003/100000000000000 : ℝ)^6207
        have hw : |(-1922776369/10000000000 : ℝ)|=(1922776369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200977657/2500000000 : ℝ)|^8255 ≤ (37717000264513/100000000000000 : ℝ)^6207
        have hw : |(1200977657/2500000000 : ℝ)|=(1200977657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6038190689/10000000000 : ℝ)|^8255 ≤ (6390385112259/12500000000000 : ℝ)^6207
        have hw : |(6038190689/10000000000 : ℝ)|=(6038190689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (206709497/400000000 : ℝ)*x 0 + (-21866499/156250000 : ℝ)*x 1 + (3019094361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206709497/400000000 : ℝ)^8255 ≤ (20781357178031/50000000000000 : ℝ)^6207 := by
    have hnat : (206709497 : ℕ)^8255*50000000000000^6207 ≤ 20781357178031^6207*400000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206709497 400000000 20781357178031 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21866499/156250000 : ℝ)^8255 ≤ (7314226885401/100000000000000 : ℝ)^6207 := by
    have hnat : (21866499 : ℕ)^8255*100000000000000^6207 ≤ 7314226885401^6207*156250000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21866499 156250000 7314226885401 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3019094361/5000000000 : ℝ)^8255 ≤ (51123058749289/100000000000000 : ℝ)^6207 := by
    have hnat : (3019094361 : ℕ)^8255*100000000000000^6207 ≤ 51123058749289^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019094361 5000000000 51123058749289 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206709497/400000000 : ℝ), (-21866499/156250000 : ℝ), (3019094361/5000000000 : ℝ)] ![(20781357178031/50000000000000 : ℝ), (7314226885401/100000000000000 : ℝ), (51123058749289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206709497/400000000 : ℝ)|^8255 ≤ (20781357178031/50000000000000 : ℝ)^6207
        have hw : |(206709497/400000000 : ℝ)|=(206709497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21866499/156250000 : ℝ)|^8255 ≤ (7314226885401/100000000000000 : ℝ)^6207
        have hw : |(-21866499/156250000 : ℝ)|=(21866499/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3019094361/5000000000 : ℝ)|^8255 ≤ (51123058749289/100000000000000 : ℝ)^6207
        have hw : |(3019094361/5000000000 : ℝ)|=(3019094361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583868989/5000000000 : ℝ)*x 0 + (1207637883/2000000000 : ℝ)*x 1 + (-1399453961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583868989/5000000000 : ℝ)^8255 ≤ (41562720271187/100000000000000 : ℝ)^6207 := by
    have hnat : (2583868989 : ℕ)^8255*100000000000000^6207 ≤ 41562720271187^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583868989 5000000000 41562720271187 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207637883/2000000000 : ℝ)^8255 ≤ (51123066552597/100000000000000 : ℝ)^6207 := by
    have hnat : (1207637883 : ℕ)^8255*100000000000000^6207 ≤ 51123066552597^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207637883 2000000000 51123066552597 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399453961/10000000000 : ℝ)^8255 ≤ (7314213157267/100000000000000 : ℝ)^6207 := by
    have hnat : (1399453961 : ℕ)^8255*100000000000000^6207 ≤ 7314213157267^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399453961 10000000000 7314213157267 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583868989/5000000000 : ℝ), (1207637883/2000000000 : ℝ), (-1399453961/10000000000 : ℝ)] ![(41562720271187/100000000000000 : ℝ), (51123066552597/100000000000000 : ℝ), (7314213157267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583868989/5000000000 : ℝ)|^8255 ≤ (41562720271187/100000000000000 : ℝ)^6207
        have hw : |(2583868989/5000000000 : ℝ)|=(2583868989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1207637883/2000000000 : ℝ)|^8255 ≤ (51123066552597/100000000000000 : ℝ)^6207
        have hw : |(1207637883/2000000000 : ℝ)|=(1207637883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1399453961/10000000000 : ℝ)|^8255 ≤ (7314213157267/100000000000000 : ℝ)^6207
        have hw : |(-1399453961/10000000000 : ℝ)|=(1399453961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s0_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4218086571/10000000000 : ℝ)*x 0 + (561035253/1000000000 : ℝ)*x 1 + (399157591/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4218086571/10000000000 : ℝ)^8255 ≤ (15863255806217/50000000000000 : ℝ)^6207 := by
    have hnat : (4218086571 : ℕ)^8255*50000000000000^6207 ≤ 15863255806217^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218086571 10000000000 15863255806217 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561035253/1000000000 : ℝ)^8255 ≤ (46362776620951/100000000000000 : ℝ)^6207 := by
    have hnat : (561035253 : ℕ)^8255*100000000000000^6207 ≤ 46362776620951^6207*1000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561035253 1000000000 46362776620951 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399157591/1250000000 : ℝ)^8255 ≤ (21910711756369/100000000000000 : ℝ)^6207 := by
    have hnat : (399157591 : ℕ)^8255*100000000000000^6207 ≤ 21910711756369^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399157591 1250000000 21910711756369 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4218086571/10000000000 : ℝ), (561035253/1000000000 : ℝ), (399157591/1250000000 : ℝ)] ![(15863255806217/50000000000000 : ℝ), (46362776620951/100000000000000 : ℝ), (21910711756369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4218086571/10000000000 : ℝ)|^8255 ≤ (15863255806217/50000000000000 : ℝ)^6207
        have hw : |(4218086571/10000000000 : ℝ)|=(4218086571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561035253/1000000000 : ℝ)|^8255 ≤ (46362776620951/100000000000000 : ℝ)^6207
        have hw : |(561035253/1000000000 : ℝ)|=(561035253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(399157591/1250000000 : ℝ)|^8255 ≤ (21910711756369/100000000000000 : ℝ)^6207
        have hw : |(399157591/1250000000 : ℝ)|=(399157591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9/32 : ℝ)*pair X 0 0 := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4127/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4127 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4127*1^1024 ≤ 0^1024*1^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4127/1024 : ℝ) ≤ (2489963342020810589/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4127 ≤ (2489963342020810589/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4127*100000000000000000000^1024 ≤ 2489963342020810589^1024*5^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2489963342020810589 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2489963342020810589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4127 := by
      have hnat : (1 : ℕ)^1024*1^4127 ≤ 1^4127*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102489963342020810589/100000000000000000000 : ℝ) ≤ (10061211445895531/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (102489963342020810589/100000000000000000000 : ℝ)^1024 ≤ (10061211445895531/10000000000000000 : ℝ)^4127 := by
      have hnat : (102489963342020810589 : ℕ)^1024*10000000000000000^4127 ≤ 10061211445895531^4127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102489963342020810589 100000000000000000000 10061211445895531 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061211445895531/10000000000000000 : ℝ)) (X := (102489963342020810589/100000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52489963342020810589/50000000000000000000 : ℝ) ≤ (5061211445895531/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (52489963342020810589/50000000000000000000 : ℝ)^1024 ≤ (5061211445895531/5000000000000000 : ℝ)^4127 := by
      have hnat : (52489963342020810589 : ℕ)^1024*5000000000000000^4127 ≤ 5061211445895531^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52489963342020810589 50000000000000000000 5061211445895531 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061211445895531/5000000000000000 : ℝ)) (X := (52489963342020810589/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61211445895531/4000000000000000 : ℝ)*(0 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(61211445895531/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2489963342020810589/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61211445895531/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (1 : ℝ)+(61211445895531/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061211445895531/10000000000000000 : ℝ) by norm_num, show 1+(2489963342020810589/100000000000000000000 : ℝ)+(0 : ℝ)=(102489963342020810589/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2489963342020810589/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61211445895531/4000000000000000 : ℝ)*(2/5 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(61211445895531/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061211445895531/5000000000000000 : ℝ) by norm_num, show 1+2*(2489963342020810589/100000000000000000000 : ℝ)=(52489963342020810589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61211445895531/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61211445895531/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61211445895531/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61211445895531/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61211445895531/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61211445895531/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1917389023/10000000000 : ℝ)*X 0 0+(6073006949/10000000000 : ℝ)*X 0 1+(1192567989/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1104260231/2000000000 : ℝ)*X 1 0+(-266737089/1000000000 : ℝ)*X 1 1+(4770268881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1380324271/2500000000 : ℝ)*X 2 0+(4770272021/10000000000 : ℝ)*X 2 1+(-2667372261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33660339/80000000 : ℝ)*X 0 0+(1562541493/5000000000 : ℝ)*X 0 1+(2838113531/5000000000 : ℝ)*X 0 2+(33660339/80000000 : ℝ)*X 1 0+(1562541493/5000000000 : ℝ)*X 1 1+(2838113531/5000000000 : ℝ)*X 1 2+(33660339/80000000 : ℝ)*X 2 0+(1562541493/5000000000 : ℝ)*X 2 1+(2838113531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1922776369/10000000000 : ℝ)*X 0 0+(1200977657/2500000000 : ℝ)*X 0 1+(6038190689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((206709497/400000000 : ℝ)*X 1 0+(-21866499/156250000 : ℝ)*X 1 1+(3019094361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583868989/5000000000 : ℝ)*X 2 0+(1207637883/2000000000 : ℝ)*X 2 1+(-1399453961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4218086571/10000000000 : ℝ)*X 0 0+(561035253/1000000000 : ℝ)*X 0 1+(399157591/1250000000 : ℝ)*X 0 2+(4218086571/10000000000 : ℝ)*X 1 0+(561035253/1000000000 : ℝ)*X 1 1+(399157591/1250000000 : ℝ)*X 1 2+(4218086571/10000000000 : ℝ)*X 2 0+(561035253/1000000000 : ℝ)*X 2 1+(399157591/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108640729978020335443491/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (681444677/100000000000000 : ℝ)*(base19) + (267892273/100000000000000 : ℝ)*(base23) + (19681757/25000000000000 : ℝ)*(base37) + (39303371/100000000000000 : ℝ)*(base51) + (150067647/100000000000000 : ℝ)*(base59) + (289899977375613/50000000000000 : ℝ)*(major0) + (289899977375613/50000000000000 : ℝ)*(major1) + (289899977375613/50000000000000 : ℝ)*(major2) + (383808824634617/50000000000000 : ℝ)*(sp0) + (191904479223957/25000000000000 : ℝ)*(sp1) + (383808789026893/50000000000000 : ℝ)*(sp2) + (195990580003881/50000000000000 : ℝ)*(sp3) + (118633909/12500000000000 : ℝ)*(sp4) + (752394447/100000000000000 : ℝ)*(sp6) + (39198123873479/10000000000000 : ℝ)*(f.failure) + (383809299170253/50000000000000 : ℝ)*(f.sum) + (355897445085503/100000000000000000000000000000 : ℝ)*base65 + (236465302285503/200000000000000000000000000000 : ℝ)*base67 + (889078726114497/200000000000000000000000000000 : ℝ)*base70 + (377130727085503/200000000000000000000000000000 : ℝ)*base71 + (7680903885503/100000000000000000000000000000 : ℝ)*base73 + (351813202685503/200000000000000000000000000000 : ℝ)*base75 + (360313357085503/200000000000000000000000000000 : ℝ)*base77 + (88517523514497/200000000000000000000000000000 : ℝ)*base80 + (60217108014497/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1058649/1000000000000000000000 : ℝ)*base89 + (1058649/1000000000000000000000 : ℝ)*base91 + (1058649/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1465507524292908242007399/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5065951/12500000000000 : ℝ)*(base1) + (1661020543/100000000000000 : ℝ)*(base19) + (1807223699/100000000000000 : ℝ)*(base23) + (284150041/100000000000000 : ℝ)*(base45) + (47519931/25000000000000 : ℝ)*(upper3) + (313392269/100000000000000 : ℝ)*(upper5) + (611953366842343/100000000000000 : ℝ)*(major0) + (611953366842343/100000000000000 : ℝ)*(major1) + (611953366842343/100000000000000 : ℝ)*(major2) + (217436643/25000000000000 : ℝ)*(sp2) + (202546890552063/25000000000000 : ℝ)*(sp4) + (405092930330051/50000000000000 : ℝ)*(sp5) + (405092422355187/50000000000000 : ℝ)*(sp6) + (16548757089007/4000000000000 : ℝ)*(sp7) + (206859483876391/50000000000000 : ℝ)*(f.failure) + (162037504336129/20000000000000 : ℝ)*(f.sum) + (398868262130867/200000000000000000000000000000 : ℝ)*base66 + (763559322869133/400000000000000000000000000000 : ℝ)*base67 + (2225539885930867/400000000000000000000000000000 : ℝ)*base70 + (2395359584730867/400000000000000000000000000000 : ℝ)*base72 + (549041869669133/200000000000000000000000000000 : ℝ)*base73 + (572101492330867/400000000000000000000000000000 : ℝ)*base76 + (2244664572730867/400000000000000000000000000000 : ℝ)*base78 + (783501063530867/400000000000000000000000000000 : ℝ)*base80 + (453637986469133/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (211321/5000000000000000000000 : ℝ)*base89 + (211321/5000000000000000000000 : ℝ)*base91 + (211321/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1062_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9/32 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1062_s1_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063902983/5000000000 : ℝ)*x 0 + (2861722837/5000000000 : ℝ)*x 1 + (2492538937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063902983/5000000000 : ℝ)^8255 ≤ (510790894037/4000000000000 : ℝ)^6207 := by
    have hnat : (1063902983 : ℕ)^8255*4000000000000^6207 ≤ 510790894037^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063902983 5000000000 510790894037 4000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2861722837/5000000000 : ℝ)^8255 ≤ (1487807304179/3125000000000 : ℝ)^6207 := by
    have hnat : (2861722837 : ℕ)^8255*3125000000000^6207 ≤ 1487807304179^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861722837 5000000000 1487807304179 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2492538937/5000000000 : ℝ)^8255 ≤ (39620393895197/100000000000000 : ℝ)^6207 := by
    have hnat : (2492538937 : ℕ)^8255*100000000000000^6207 ≤ 39620393895197^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492538937 5000000000 39620393895197 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063902983/5000000000 : ℝ), (2861722837/5000000000 : ℝ), (2492538937/5000000000 : ℝ)] ![(510790894037/4000000000000 : ℝ), (1487807304179/3125000000000 : ℝ), (39620393895197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063902983/5000000000 : ℝ)|^8255 ≤ (510790894037/4000000000000 : ℝ)^6207
        have hw : |(-1063902983/5000000000 : ℝ)|=(1063902983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2861722837/5000000000 : ℝ)|^8255 ≤ (1487807304179/3125000000000 : ℝ)^6207
        have hw : |(2861722837/5000000000 : ℝ)|=(2861722837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2492538937/5000000000 : ℝ)|^8255 ≤ (39620393895197/100000000000000 : ℝ)^6207
        have hw : |(2492538937/5000000000 : ℝ)|=(2492538937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108470697/200000000 : ℝ)*x 0 + (-505587913/2000000000 : ℝ)*x 1 + (4985078197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108470697/200000000 : ℝ)^8255 ≤ (22160467290431/50000000000000 : ℝ)^6207 := by
    have hnat : (108470697 : ℕ)^8255*50000000000000^6207 ≤ 22160467290431^6207*200000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108470697 200000000 22160467290431 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505587913/2000000000 : ℝ)^8255 ≤ (16058668087591/100000000000000 : ℝ)^6207 := by
    have hnat : (505587913 : ℕ)^8255*100000000000000^6207 ≤ 16058668087591^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505587913 2000000000 16058668087591 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4985078197/10000000000 : ℝ)^8255 ≤ (39620397309363/100000000000000 : ℝ)^6207 := by
    have hnat : (4985078197 : ℕ)^8255*100000000000000^6207 ≤ 39620397309363^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985078197 10000000000 39620397309363 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108470697/200000000 : ℝ), (-505587913/2000000000 : ℝ), (4985078197/10000000000 : ℝ)] ![(22160467290431/50000000000000 : ℝ), (16058668087591/100000000000000 : ℝ), (39620397309363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108470697/200000000 : ℝ)|^8255 ≤ (22160467290431/50000000000000 : ℝ)^6207
        have hw : |(108470697/200000000 : ℝ)|=(108470697/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505587913/2000000000 : ℝ)|^8255 ≤ (16058668087591/100000000000000 : ℝ)^6207
        have hw : |(-505587913/2000000000 : ℝ)|=(505587913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4985078197/10000000000 : ℝ)|^8255 ≤ (39620397309363/100000000000000 : ℝ)^6207
        have hw : |(4985078197/10000000000 : ℝ)|=(4985078197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711767693/5000000000 : ℝ)*x 0 + (4985077579/10000000000 : ℝ)*x 1 + (-50558793/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711767693/5000000000 : ℝ)^8255 ≤ (44320940406273/100000000000000 : ℝ)^6207 := by
    have hnat : (2711767693 : ℕ)^8255*100000000000000^6207 ≤ 44320940406273^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711767693 5000000000 44320940406273 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4985077579/10000000000 : ℝ)^8255 ≤ (7924078155399/20000000000000 : ℝ)^6207 := by
    have hnat : (4985077579 : ℕ)^8255*20000000000000^6207 ≤ 7924078155399^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985077579 10000000000 7924078155399 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50558793/200000000 : ℝ)^8255 ≤ (16058668805711/100000000000000 : ℝ)^6207 := by
    have hnat : (50558793 : ℕ)^8255*100000000000000^6207 ≤ 16058668805711^6207*200000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50558793 200000000 16058668805711 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711767693/5000000000 : ℝ), (4985077579/10000000000 : ℝ), (-50558793/200000000 : ℝ)] ![(44320940406273/100000000000000 : ℝ), (7924078155399/20000000000000 : ℝ), (16058668805711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711767693/5000000000 : ℝ)|^8255 ≤ (44320940406273/100000000000000 : ℝ)^6207
        have hw : |(2711767693/5000000000 : ℝ)|=(2711767693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4985077579/10000000000 : ℝ)|^8255 ≤ (7924078155399/20000000000000 : ℝ)^6207
        have hw : |(4985077579/10000000000 : ℝ)|=(4985077579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50558793/200000000 : ℝ)|^8255 ≤ (16058668805711/100000000000000 : ℝ)^6207
        have hw : |(-50558793/200000000 : ℝ)|=(50558793/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2162066599/5000000000 : ℝ)*x 0 + (1830884039/5000000000 : ℝ)*x 1 + (79808059/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162066599/5000000000 : ℝ)^8255 ≤ (32791700490857/100000000000000 : ℝ)^6207 := by
    have hnat : (2162066599 : ℕ)^8255*100000000000000^6207 ≤ 32791700490857^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162066599 5000000000 32791700490857 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830884039/5000000000 : ℝ)^8255 ≤ (6571592256329/25000000000000 : ℝ)^6207 := by
    have hnat : (1830884039 : ℕ)^8255*25000000000000^6207 ≤ 6571592256329^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830884039 5000000000 6571592256329 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79808059/156250000 : ℝ)^8255 ≤ (20460965235797/50000000000000 : ℝ)^6207 := by
    have hnat : (79808059 : ℕ)^8255*50000000000000^6207 ≤ 20460965235797^6207*156250000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79808059 156250000 20460965235797 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162066599/5000000000 : ℝ), (1830884039/5000000000 : ℝ), (79808059/156250000 : ℝ)] ![(32791700490857/100000000000000 : ℝ), (6571592256329/25000000000000 : ℝ), (20460965235797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162066599/5000000000 : ℝ)|^8255 ≤ (32791700490857/100000000000000 : ℝ)^6207
        have hw : |(2162066599/5000000000 : ℝ)|=(2162066599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1830884039/5000000000 : ℝ)|^8255 ≤ (6571592256329/25000000000000 : ℝ)^6207
        have hw : |(1830884039/5000000000 : ℝ)|=(1830884039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79808059/156250000 : ℝ)|^8255 ≤ (20460965235797/50000000000000 : ℝ)^6207
        have hw : |(79808059/156250000 : ℝ)|=(79808059/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128734369/10000000000 : ℝ)*x 0 + (999094027/2000000000 : ℝ)*x 1 + (5712839883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128734369/10000000000 : ℝ)^8255 ≤ (1277718296603/10000000000000 : ℝ)^6207 := by
    have hnat : (2128734369 : ℕ)^8255*10000000000000^6207 ≤ 1277718296603^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128734369 10000000000 1277718296603 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999094027/2000000000 : ℝ)^8255 ≤ (3973027967299/10000000000000 : ℝ)^6207 := by
    have hnat : (999094027 : ℕ)^8255*10000000000000^6207 ≤ 3973027967299^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999094027 2000000000 3973027967299 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5712839883/10000000000 : ℝ)^8255 ≤ (47492537341339/100000000000000 : ℝ)^6207 := by
    have hnat : (5712839883 : ℕ)^8255*100000000000000^6207 ≤ 47492537341339^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712839883 10000000000 47492537341339 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128734369/10000000000 : ℝ), (999094027/2000000000 : ℝ), (5712839883/10000000000 : ℝ)] ![(1277718296603/10000000000000 : ℝ), (3973027967299/10000000000000 : ℝ), (47492537341339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128734369/10000000000 : ℝ)|^8255 ≤ (1277718296603/10000000000000 : ℝ)^6207
        have hw : |(-2128734369/10000000000 : ℝ)|=(2128734369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999094027/2000000000 : ℝ)|^8255 ≤ (3973027967299/10000000000000 : ℝ)^6207
        have hw : |(999094027/2000000000 : ℝ)|=(999094027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5712839883/10000000000 : ℝ)|^8255 ≤ (47492537341339/100000000000000 : ℝ)^6207
        have hw : |(5712839883/10000000000 : ℝ)|=(5712839883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5235006449/10000000000 : ℝ)*x 0 + (-112510987/625000000 : ℝ)*x 1 + (2856420749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235006449/10000000000 : ℝ)^8255 ≤ (2114189670321/5000000000000 : ℝ)^6207 := by
    have hnat : (5235006449 : ℕ)^8255*5000000000000^6207 ≤ 2114189670321^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235006449 10000000000 2114189670321 5000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112510987/625000000 : ℝ)^8255 ≤ (10223651385477/100000000000000 : ℝ)^6207 := by
    have hnat : (112510987 : ℕ)^8255*100000000000000^6207 ≤ 10223651385477^6207*625000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112510987 625000000 10223651385477 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856420749/5000000000 : ℝ)^8255 ≤ (1484142349913/3125000000000 : ℝ)^6207 := by
    have hnat : (2856420749 : ℕ)^8255*3125000000000^6207 ≤ 1484142349913^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856420749 5000000000 1484142349913 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235006449/10000000000 : ℝ), (-112510987/625000000 : ℝ), (2856420749/5000000000 : ℝ)] ![(2114189670321/5000000000000 : ℝ), (10223651385477/100000000000000 : ℝ), (1484142349913/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235006449/10000000000 : ℝ)|^8255 ≤ (2114189670321/5000000000000 : ℝ)^6207
        have hw : |(5235006449/10000000000 : ℝ)|=(5235006449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112510987/625000000 : ℝ)|^8255 ≤ (10223651385477/100000000000000 : ℝ)^6207
        have hw : |(-112510987/625000000 : ℝ)|=(112510987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856420749/5000000000 : ℝ)|^8255 ≤ (1484142349913/3125000000000 : ℝ)^6207
        have hw : |(2856420749/5000000000 : ℝ)|=(2856420749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1308751109/2500000000 : ℝ)*x 0 + (5712843717/10000000000 : ℝ)*x 1 + (-1800175407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308751109/2500000000 : ℝ)^8255 ≤ (1321367868201/3125000000000 : ℝ)^6207 := by
    have hnat : (1308751109 : ℕ)^8255*3125000000000^6207 ≤ 1321367868201^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308751109 2500000000 1321367868201 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5712843717/10000000000 : ℝ)^8255 ≤ (11873144932771/25000000000000 : ℝ)^6207 := by
    have hnat : (5712843717 : ℕ)^8255*25000000000000^6207 ≤ 11873144932771^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712843717 10000000000 11873144932771 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800175407/10000000000 : ℝ)^8255 ≤ (408945939101/4000000000000 : ℝ)^6207 := by
    have hnat : (1800175407 : ℕ)^8255*4000000000000^6207 ≤ 408945939101^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800175407 10000000000 408945939101 4000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308751109/2500000000 : ℝ), (5712843717/10000000000 : ℝ), (-1800175407/10000000000 : ℝ)] ![(1321367868201/3125000000000 : ℝ), (11873144932771/25000000000000 : ℝ), (408945939101/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308751109/2500000000 : ℝ)|^8255 ≤ (1321367868201/3125000000000 : ℝ)^6207
        have hw : |(1308751109/2500000000 : ℝ)|=(1308751109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5712843717/10000000000 : ℝ)|^8255 ≤ (11873144932771/25000000000000 : ℝ)^6207
        have hw : |(5712843717/10000000000 : ℝ)|=(5712843717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1800175407/10000000000 : ℝ)|^8255 ≤ (408945939101/4000000000000 : ℝ)^6207
        have hw : |(-1800175407/10000000000 : ℝ)|=(1800175407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s1_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081486869/2500000000 : ℝ)*x 0 + (2543680561/5000000000 : ℝ)*x 1 + (3682534129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081486869/2500000000 : ℝ)^8255 ≤ (32809999774941/100000000000000 : ℝ)^6207 := by
    have hnat : (1081486869 : ℕ)^8255*100000000000000^6207 ≤ 32809999774941^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081486869 2500000000 32809999774941 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543680561/5000000000 : ℝ)^8255 ≤ (40705188721063/100000000000000 : ℝ)^6207 := by
    have hnat : (2543680561 : ℕ)^8255*100000000000000^6207 ≤ 40705188721063^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543680561 5000000000 40705188721063 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3682534129/10000000000 : ℝ)^8255 ≤ (1324240574887/5000000000000 : ℝ)^6207 := by
    have hnat : (3682534129 : ℕ)^8255*5000000000000^6207 ≤ 1324240574887^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682534129 10000000000 1324240574887 5000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081486869/2500000000 : ℝ), (2543680561/5000000000 : ℝ), (3682534129/10000000000 : ℝ)] ![(32809999774941/100000000000000 : ℝ), (40705188721063/100000000000000 : ℝ), (1324240574887/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081486869/2500000000 : ℝ)|^8255 ≤ (32809999774941/100000000000000 : ℝ)^6207
        have hw : |(1081486869/2500000000 : ℝ)|=(1081486869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543680561/5000000000 : ℝ)|^8255 ≤ (40705188721063/100000000000000 : ℝ)^6207
        have hw : |(2543680561/5000000000 : ℝ)|=(2543680561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3682534129/10000000000 : ℝ)|^8255 ≤ (1324240574887/5000000000000 : ℝ)^6207
        have hw : |(3682534129/10000000000 : ℝ)|=(3682534129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9/32 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (519/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2081/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9/32 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9/32 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9/32 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9/32 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9/32 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9/32 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1/1250 : ℝ) ^ (4127/1024 : ℝ) ≤ (4125873/12500000000000000000 : ℝ) := by
    have hpowers : (1/1250 : ℝ)^4127 ≤ (4125873/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1 : ℕ)^4127*12500000000000000000^1024 ≤ 4125873^1024*1250^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1250 4125873 12500000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/1250 : ℝ)) (X := (4125873/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9/32 : ℝ) ^ (4127/1024 : ℝ) ≤ (602132767364062961/100000000000000000000 : ℝ) := by
    have hpowers : (9/32 : ℝ)^4127 ≤ (602132767364062961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9 : ℕ)^4127*100000000000000000000^1024 ≤ 602132767364062961^1024*32^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 32 602132767364062961 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/32 : ℝ)) (X := (602132767364062961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000000004125873/6250000000000000000 : ℝ) ≤ (5000000000000819/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (6250000000004125873/6250000000000000000 : ℝ)^1024 ≤ (5000000000000819/5000000000000000 : ℝ)^4127 := by
      have hnat : (6250000000004125873 : ℕ)^1024*5000000000000000^4127 ≤ 5000000000000819^4127*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000000004125873 6250000000000000000 5000000000000819 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000000819/5000000000000000 : ℝ)) (X := (6250000000004125873/6250000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20120426553479413989/20000000000000000000 : ℝ) ≤ (2503726636237259/2500000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (20120426553479413989/20000000000000000000 : ℝ)^1024 ≤ (2503726636237259/2500000000000000 : ℝ)^4127 := by
      have hnat : (20120426553479413989 : ℕ)^1024*2500000000000000^4127 ≤ 2503726636237259^4127*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20120426553479413989 20000000000000000000 2503726636237259 2500000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503726636237259/2500000000000000 : ℝ)) (X := (20120426553479413989/20000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50602132767364062961/50000000000000000000 : ℝ) ≤ (5014906544948217/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50602132767364062961/50000000000000000000 : ℝ)^1024 ≤ (5014906544948217/5000000000000000 : ℝ)^4127 := by
      have hnat : (50602132767364062961 : ℕ)^1024*5000000000000000^4127 ≤ 5014906544948217^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50602132767364062961 50000000000000000000 5014906544948217 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014906544948217/5000000000000000 : ℝ)) (X := (50602132767364062961/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4125873/12500000000000000000 : ℝ) ≤ ((28044761495285435403/28045000000000000000 : ℝ)+2*(7453272473699/1402250000000000 : ℝ)*(1/1250 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (28044761495285435403/28045000000000000000 : ℝ)+2*(7453272473699/1402250000000000 : ℝ)*(1/1250 : ℝ)=(5000000000000819/5000000000000000 : ℝ) by norm_num, show 1+2*(4125873/12500000000000000000 : ℝ)=(6250000000004125873/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(602132767364062961/100000000000000000000 : ℝ)+(4125873/12500000000000000000 : ℝ) ≤ ((28044761495285435403/28045000000000000000 : ℝ)+(7453272473699/1402250000000000 : ℝ)*((9/32 : ℝ)+(1/1250 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (28044761495285435403/28045000000000000000 : ℝ)+(7453272473699/1402250000000000 : ℝ)*((9/32 : ℝ)+(1/1250 : ℝ))=(2503726636237259/2500000000000000 : ℝ) by norm_num, show 1+(602132767364062961/100000000000000000000 : ℝ)+(4125873/12500000000000000000 : ℝ)=(20120426553479413989/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(602132767364062961/100000000000000000000 : ℝ) ≤ ((28044761495285435403/28045000000000000000 : ℝ)+2*(7453272473699/1402250000000000 : ℝ)*(9/32 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (28044761495285435403/28045000000000000000 : ℝ)+2*(7453272473699/1402250000000000 : ℝ)*(9/32 : ℝ)=(5014906544948217/5000000000000000 : ℝ) by norm_num, show 1+2*(602132767364062961/100000000000000000000 : ℝ)=(50602132767364062961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28044761495285435403/28045000000000000000 : ℝ)*(X 1 0+X 2 0)+(7453272473699/1402250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (1/1250 : ℝ)) (hi := (9/32 : ℝ)) (c := (28044761495285435403/28045000000000000000 : ℝ)) (alpha := (7453272473699/1402250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28044761495285435403/28045000000000000000 : ℝ)*(X 0 1+X 2 1)+(7453272473699/1402250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (1/1250 : ℝ)) (hi := (9/32 : ℝ)) (c := (28044761495285435403/28045000000000000000 : ℝ)) (alpha := (7453272473699/1402250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28044761495285435403/28045000000000000000 : ℝ)*(X 0 2+X 1 2)+(7453272473699/1402250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (1/1250 : ℝ)) (hi := (9/32 : ℝ)) (c := (28044761495285435403/28045000000000000000 : ℝ)) (alpha := (7453272473699/1402250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1063902983/5000000000 : ℝ)*X 0 0+(2861722837/5000000000 : ℝ)*X 0 1+(2492538937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((108470697/200000000 : ℝ)*X 1 0+(-505587913/2000000000 : ℝ)*X 1 1+(4985078197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711767693/5000000000 : ℝ)*X 2 0+(4985077579/10000000000 : ℝ)*X 2 1+(-50558793/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162066599/5000000000 : ℝ)*X 0 0+(1830884039/5000000000 : ℝ)*X 0 1+(79808059/156250000 : ℝ)*X 0 2+(2162066599/5000000000 : ℝ)*X 1 0+(1830884039/5000000000 : ℝ)*X 1 1+(79808059/156250000 : ℝ)*X 1 2+(2162066599/5000000000 : ℝ)*X 2 0+(1830884039/5000000000 : ℝ)*X 2 1+(79808059/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128734369/10000000000 : ℝ)*X 0 0+(999094027/2000000000 : ℝ)*X 0 1+(5712839883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5235006449/10000000000 : ℝ)*X 1 0+(-112510987/625000000 : ℝ)*X 1 1+(2856420749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1308751109/2500000000 : ℝ)*X 2 0+(5712843717/10000000000 : ℝ)*X 2 1+(-1800175407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081486869/2500000000 : ℝ)*X 0 0+(2543680561/5000000000 : ℝ)*X 0 1+(3682534129/10000000000 : ℝ)*X 0 2+(1081486869/2500000000 : ℝ)*X 1 0+(2543680561/5000000000 : ℝ)*X 1 1+(3682534129/10000000000 : ℝ)*X 1 2+(1081486869/2500000000 : ℝ)*X 2 0+(2543680561/5000000000 : ℝ)*X 2 1+(3682534129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1472359002325108578114836271/701125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17404719/25000000000000 : ℝ)*(base1) + (224133643/50000000000000 : ℝ)*(base19) + (36382187/6250000000000 : ℝ)*(base23) + (45161317/100000000000000 : ℝ)*(upper3) + (5316017/10000000000000 : ℝ)*(upper5) + (1022966545716281/100000000000000 : ℝ)*(major0) + (1022966545716281/100000000000000 : ℝ)*(major1) + (1022966545716281/100000000000000 : ℝ)*(major2) + (677170384549447/50000000000000 : ℝ)*(sp0) + (677171421915847/50000000000000 : ℝ)*(sp1) + (338585677495997/25000000000000 : ℝ)*(sp2) + (138317748155979/20000000000000 : ℝ)*(sp3) + (2592618963/100000000000000 : ℝ)*(sp4) + (229733743/25000000000000 : ℝ)*(sp7) + (691589729333743/100000000000000 : ℝ)*(f.failure) + (67717164604949/5000000000000 : ℝ)*(f.sum) + (224900229462363/140225000000000000000000000000 : ℝ)*base65 + (6040073165161776243/2804500000000000000000000000000000 : ℝ)*base67 + (5632958749109223757/2804500000000000000000000000000000 : ℝ)*base70 + (1159637878340276243/2804500000000000000000000000000000 : ℝ)*base71 + (440924838768969/70112500000000000000000000000 : ℝ)*base73 + (19463942344842276243/2804500000000000000000000000000000 : ℝ)*base75 + (16674514782334276243/2804500000000000000000000000000000 : ℝ)*base77 + (8328123113152276243/2804500000000000000000000000000000 : ℝ)*base79 + (37365602428769/70112500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (28060367/10000000000000000000000 : ℝ)*base90 + (28060367/10000000000000000000000 : ℝ)*base92 + (28060367/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24348845203065554984277/28045000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2001576033/100000000000000 : ℝ)*(base19) + (1956817989/100000000000000 : ℝ)*(base23) + (58657507/25000000000000 : ℝ)*(upper2) + (342204771/100000000000000 : ℝ)*(upper3) + (59419463/12500000000000 : ℝ)*(upper5) + (210581051656277/20000000000000 : ℝ)*(major0) + (210581051656277/20000000000000 : ℝ)*(major1) + (210581051656277/20000000000000 : ℝ)*(major2) + (101822999/1000000000000 : ℝ)*(sp1) + (5689045231/50000000000000 : ℝ)*(sp2) + (174247538181831/12500000000000 : ℝ)*(sp4) + (278793624315743/20000000000000 : ℝ)*(sp5) + (1393966970546197/100000000000000 : ℝ)*(sp6) + (71183018216791/10000000000000 : ℝ)*(sp7) + (71183018216791/10000000000000 : ℝ)*(f.failure) + (174247538181831/12500000000000 : ℝ)*(f.sum) + (68896851380543/14022500000000000000000000000 : ℝ)*base65 + (916640085834565369/560900000000000000000000000000000 : ℝ)*base68 + (1658314831941165369/560900000000000000000000000000000 : ℝ)*base70 + (285418705339934631/560900000000000000000000000000000 : ℝ)*base71 + (6711464253223/14022500000000000000000000000 : ℝ)*base73 + (3671199378368565369/560900000000000000000000000000000 : ℝ)*base76 + (1117586666329834631/560900000000000000000000000000000 : ℝ)*base77 + (284410447205134631/560900000000000000000000000000000 : ℝ)*base79 + (11010455211749/28045000000000000000000000000 : ℝ)*base82 + (1156279/1000000000000000000000 : ℝ)*base90 + (1156279/1000000000000000000000 : ℝ)*base92 + (1156279/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1062_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9/32 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (519/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2081/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1062_s2_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092728119/5000000000 : ℝ)*x 0 + (5526731631/10000000000 : ℝ)*x 1 + (5145219941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092728119/5000000000 : ℝ)^8255 ≤ (2646390894711/20000000000000 : ℝ)^6207 := by
    have hnat : (1092728119 : ℕ)^8255*20000000000000^6207 ≤ 2646390894711^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092728119 5000000000 2646390894711 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526731631/10000000000 : ℝ)^8255 ≤ (2840375906619/6250000000000 : ℝ)^6207 := by
    have hnat : (5526731631 : ℕ)^8255*6250000000000^6207 ≤ 2840375906619^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526731631 10000000000 2840375906619 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5145219941/10000000000 : ℝ)^8255 ≤ (5165253875619/12500000000000 : ℝ)^6207 := by
    have hnat : (5145219941 : ℕ)^8255*12500000000000^6207 ≤ 5165253875619^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145219941 10000000000 5165253875619 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092728119/5000000000 : ℝ), (5526731631/10000000000 : ℝ), (5145219941/10000000000 : ℝ)] ![(2646390894711/20000000000000 : ℝ), (2840375906619/6250000000000 : ℝ), (5165253875619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092728119/5000000000 : ℝ)|^8255 ≤ (2646390894711/20000000000000 : ℝ)^6207
        have hw : |(-1092728119/5000000000 : ℝ)|=(1092728119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526731631/10000000000 : ℝ)|^8255 ≤ (2840375906619/6250000000000 : ℝ)^6207
        have hw : |(5526731631/10000000000 : ℝ)|=(5526731631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5145219941/10000000000 : ℝ)|^8255 ≤ (5165253875619/12500000000000 : ℝ)^6207
        have hw : |(5145219941/10000000000 : ℝ)|=(5145219941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377382657/10000000000 : ℝ)*x 0 + (-2384451251/10000000000 : ℝ)*x 1 + (2572610659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377382657/10000000000 : ℝ)^8255 ≤ (4382004400439/10000000000000 : ℝ)^6207 := by
    have hnat : (5377382657 : ℕ)^8255*10000000000000^6207 ≤ 4382004400439^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377382657 10000000000 4382004400439 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2384451251/10000000000 : ℝ)^8255 ≤ (14857910268829/100000000000000 : ℝ)^6207 := by
    have hnat : (2384451251 : ℕ)^8255*100000000000000^6207 ≤ 14857910268829^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384451251 10000000000 14857910268829 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2572610659/5000000000 : ℝ)^8255 ≤ (5165255714091/12500000000000 : ℝ)^6207 := by
    have hnat : (2572610659 : ℕ)^8255*12500000000000^6207 ≤ 5165255714091^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572610659 5000000000 5165255714091 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377382657/10000000000 : ℝ), (-2384451251/10000000000 : ℝ), (2572610659/5000000000 : ℝ)] ![(4382004400439/10000000000000 : ℝ), (14857910268829/100000000000000 : ℝ), (5165255714091/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377382657/10000000000 : ℝ)|^8255 ≤ (4382004400439/10000000000000 : ℝ)^6207
        have hw : |(5377382657/10000000000 : ℝ)|=(5377382657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2384451251/10000000000 : ℝ)|^8255 ≤ (14857910268829/100000000000000 : ℝ)^6207
        have hw : |(-2384451251/10000000000 : ℝ)|=(2384451251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2572610659/5000000000 : ℝ)|^8255 ≤ (5165255714091/12500000000000 : ℝ)^6207
        have hw : |(2572610659/5000000000 : ℝ)|=(2572610659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (168043213/312500000 : ℝ)*x 0 + (1029044221/2000000000 : ℝ)*x 1 + (-2384451317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168043213/312500000 : ℝ)^8255 ≤ (1369376428987/3125000000000 : ℝ)^6207 := by
    have hnat : (168043213 : ℕ)^8255*3125000000000^6207 ≤ 1369376428987^6207*312500000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168043213 312500000 1369376428987 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029044221/2000000000 : ℝ)^8255 ≤ (41322043437669/100000000000000 : ℝ)^6207 := by
    have hnat : (1029044221 : ℕ)^8255*100000000000000^6207 ≤ 41322043437669^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029044221 2000000000 41322043437669 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384451317/10000000000 : ℝ)^8255 ≤ (742895540789/5000000000000 : ℝ)^6207 := by
    have hnat : (2384451317 : ℕ)^8255*5000000000000^6207 ≤ 742895540789^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384451317 10000000000 742895540789 5000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168043213/312500000 : ℝ), (1029044221/2000000000 : ℝ), (-2384451317/10000000000 : ℝ)] ![(1369376428987/3125000000000 : ℝ), (41322043437669/100000000000000 : ℝ), (742895540789/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168043213/312500000 : ℝ)|^8255 ≤ (1369376428987/3125000000000 : ℝ)^6207
        have hw : |(168043213/312500000 : ℝ)|=(168043213/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029044221/2000000000 : ℝ)|^8255 ≤ (41322043437669/100000000000000 : ℝ)^6207
        have hw : |(1029044221/2000000000 : ℝ)|=(1029044221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2384451317/10000000000 : ℝ)|^8255 ≤ (742895540789/5000000000000 : ℝ)^6207
        have hw : |(-2384451317/10000000000 : ℝ)|=(2384451317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363459773/10000000000 : ℝ)*x 0 + (4006042951/10000000000 : ℝ)*x 1 + (297071931/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363459773/10000000000 : ℝ)^8255 ≤ (33188925094333/100000000000000 : ℝ)^6207 := by
    have hnat : (4363459773 : ℕ)^8255*100000000000000^6207 ≤ 33188925094333^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363459773 10000000000 33188925094333 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006042951/10000000000 : ℝ)^8255 ≤ (29623174137173/100000000000000 : ℝ)^6207 := by
    have hnat : (4006042951 : ℕ)^8255*100000000000000^6207 ≤ 29623174137173^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006042951 10000000000 29623174137173 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297071931/625000000 : ℝ)^8255 ≤ (743758014931/2000000000000 : ℝ)^6207 := by
    have hnat : (297071931 : ℕ)^8255*2000000000000^6207 ≤ 743758014931^6207*625000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297071931 625000000 743758014931 2000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363459773/10000000000 : ℝ), (4006042951/10000000000 : ℝ), (297071931/625000000 : ℝ)] ![(33188925094333/100000000000000 : ℝ), (29623174137173/100000000000000 : ℝ), (743758014931/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363459773/10000000000 : ℝ)|^8255 ≤ (33188925094333/100000000000000 : ℝ)^6207
        have hw : |(4363459773/10000000000 : ℝ)|=(4363459773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006042951/10000000000 : ℝ)|^8255 ≤ (29623174137173/100000000000000 : ℝ)^6207
        have hw : |(4006042951/10000000000 : ℝ)|=(4006042951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297071931/625000000 : ℝ)|^8255 ≤ (743758014931/2000000000000 : ℝ)^6207
        have hw : |(297071931/625000000 : ℝ)|=(297071931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092791613/5000000000 : ℝ)*x 0 + (2574002209/5000000000 : ℝ)*x 1 + (5523918119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092791613/5000000000 : ℝ)^8255 ≤ (13232977022399/100000000000000 : ℝ)^6207 := by
    have hnat : (1092791613 : ℕ)^8255*100000000000000^6207 ≤ 13232977022399^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092791613 5000000000 13232977022399 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574002209/5000000000 : ℝ)^8255 ≤ (41351774736311/100000000000000 : ℝ)^6207 := by
    have hnat : (2574002209 : ℕ)^8255*100000000000000^6207 ≤ 41351774736311^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574002209 5000000000 41351774736311 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5523918119/10000000000 : ℝ)^8255 ≤ (45415248221477/100000000000000 : ℝ)^6207 := by
    have hnat : (5523918119 : ℕ)^8255*100000000000000^6207 ≤ 45415248221477^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523918119 10000000000 45415248221477 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092791613/5000000000 : ℝ), (2574002209/5000000000 : ℝ), (5523918119/10000000000 : ℝ)] ![(13232977022399/100000000000000 : ℝ), (41351774736311/100000000000000 : ℝ), (45415248221477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092791613/5000000000 : ℝ)|^8255 ≤ (13232977022399/100000000000000 : ℝ)^6207
        have hw : |(-1092791613/5000000000 : ℝ)|=(1092791613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574002209/5000000000 : ℝ)|^8255 ≤ (41351774736311/100000000000000 : ℝ)^6207
        have hw : |(2574002209/5000000000 : ℝ)|=(2574002209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5523918119/10000000000 : ℝ)|^8255 ≤ (45415248221477/100000000000000 : ℝ)^6207
        have hw : |(5523918119/10000000000 : ℝ)|=(5523918119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281112357/10000000000 : ℝ)*x 0 + (-1002877763/5000000000 : ℝ)*x 1 + (27619591/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281112357/10000000000 : ℝ)^8255 ≤ (8555957831937/20000000000000 : ℝ)^6207 := by
    have hnat : (5281112357 : ℕ)^8255*20000000000000^6207 ≤ 8555957831937^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281112357 10000000000 8555957831937 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002877763/5000000000 : ℝ)^8255 ≤ (11804961724223/100000000000000 : ℝ)^6207 := by
    have hnat : (1002877763 : ℕ)^8255*100000000000000^6207 ≤ 11804961724223^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002877763 5000000000 11804961724223 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27619591/50000000 : ℝ)^8255 ≤ (2838453069197/6250000000000 : ℝ)^6207 := by
    have hnat : (27619591 : ℕ)^8255*6250000000000^6207 ≤ 2838453069197^6207*50000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27619591 50000000 2838453069197 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281112357/10000000000 : ℝ), (-1002877763/5000000000 : ℝ), (27619591/50000000 : ℝ)] ![(8555957831937/20000000000000 : ℝ), (11804961724223/100000000000000 : ℝ), (2838453069197/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281112357/10000000000 : ℝ)|^8255 ≤ (8555957831937/20000000000000 : ℝ)^6207
        have hw : |(5281112357/10000000000 : ℝ)|=(5281112357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002877763/5000000000 : ℝ)|^8255 ≤ (11804961724223/100000000000000 : ℝ)^6207
        have hw : |(-1002877763/5000000000 : ℝ)|=(1002877763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27619591/50000000 : ℝ)|^8255 ≤ (2838453069197/6250000000000 : ℝ)^6207
        have hw : |(27619591/50000000 : ℝ)|=(27619591/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281112599/10000000000 : ℝ)*x 0 + (1380979509/2500000000 : ℝ)*x 1 + (-2005755421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281112599/10000000000 : ℝ)^8255 ≤ (42779791766823/100000000000000 : ℝ)^6207 := by
    have hnat : (5281112599 : ℕ)^8255*100000000000000^6207 ≤ 42779791766823^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281112599 10000000000 42779791766823 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380979509/2500000000 : ℝ)^8255 ≤ (11353811828483/25000000000000 : ℝ)^6207 := by
    have hnat : (1380979509 : ℕ)^8255*25000000000000^6207 ≤ 11353811828483^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380979509 2500000000 11353811828483 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005755421/10000000000 : ℝ)^8255 ≤ (5902480451169/50000000000000 : ℝ)^6207 := by
    have hnat : (2005755421 : ℕ)^8255*50000000000000^6207 ≤ 5902480451169^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005755421 10000000000 5902480451169 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281112599/10000000000 : ℝ), (1380979509/2500000000 : ℝ), (-2005755421/10000000000 : ℝ)] ![(42779791766823/100000000000000 : ℝ), (11353811828483/25000000000000 : ℝ), (5902480451169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281112599/10000000000 : ℝ)|^8255 ≤ (42779791766823/100000000000000 : ℝ)^6207
        have hw : |(5281112599/10000000000 : ℝ)|=(5281112599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380979509/2500000000 : ℝ)|^8255 ≤ (11353811828483/25000000000000 : ℝ)^6207
        have hw : |(1380979509/2500000000 : ℝ)|=(1380979509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005755421/10000000000 : ℝ)|^8255 ≤ (5902480451169/50000000000000 : ℝ)^6207
        have hw : |(-2005755421/10000000000 : ℝ)|=(2005755421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s2_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181853669/5000000000 : ℝ)*x 0 + (2373851719/5000000000 : ℝ)*x 1 + (200577481/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181853669/5000000000 : ℝ)^8255 ≤ (33191429420279/100000000000000 : ℝ)^6207 := by
    have hnat : (2181853669 : ℕ)^8255*100000000000000^6207 ≤ 33191429420279^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181853669 5000000000 33191429420279 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2373851719/5000000000 : ℝ)^8255 ≤ (4641403616119/12500000000000 : ℝ)^6207 := by
    have hnat : (2373851719 : ℕ)^8255*12500000000000^6207 ≤ 4641403616119^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373851719 5000000000 4641403616119 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200577481/500000000 : ℝ)^8255 ≤ (29677341630649/100000000000000 : ℝ)^6207 := by
    have hnat : (200577481 : ℕ)^8255*100000000000000^6207 ≤ 29677341630649^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200577481 500000000 29677341630649 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181853669/5000000000 : ℝ), (2373851719/5000000000 : ℝ), (200577481/500000000 : ℝ)] ![(33191429420279/100000000000000 : ℝ), (4641403616119/12500000000000 : ℝ), (29677341630649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181853669/5000000000 : ℝ)|^8255 ≤ (33191429420279/100000000000000 : ℝ)^6207
        have hw : |(2181853669/5000000000 : ℝ)|=(2181853669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2373851719/5000000000 : ℝ)|^8255 ≤ (4641403616119/12500000000000 : ℝ)^6207
        have hw : |(2373851719/5000000000 : ℝ)|=(2373851719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200577481/500000000 : ℝ)|^8255 ≤ (29677341630649/100000000000000 : ℝ)^6207
        have hw : |(200577481/500000000 : ℝ)|=(200577481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2081/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2173/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2081/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (519/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2081/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (519/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2081/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (519/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2081/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (519/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2081/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (519/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2081/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (519/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (519/10000 : ℝ) ^ (4127/1024 : ℝ) ≤ (82924553869387/12500000000000000000 : ℝ) := by
    have hpowers : (519/10000 : ℝ)^4127 ≤ (82924553869387/12500000000000000000 : ℝ)^1024 := by
      have hnat : (519 : ℕ)^4127*12500000000000000000^1024 ≤ 82924553869387^1024*10000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        519 10000 82924553869387 12500000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (519/10000 : ℝ)) (X := (82924553869387/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2081/10000 : ℝ) ^ (4127/1024 : ℝ) ≤ (178833992877825961/100000000000000000000 : ℝ) := by
    have hpowers : (2081/10000 : ℝ)^4127 ≤ (178833992877825961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2081 : ℕ)^4127*100000000000000000000^1024 ≤ 178833992877825961^1024*10000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2081 10000 178833992877825961 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2081/10000 : ℝ)) (X := (178833992877825961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250082924553869387/6250000000000000000 : ℝ) ≤ (10000032920501911/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (6250082924553869387/6250000000000000000 : ℝ)^1024 ≤ (10000032920501911/10000000000000000 : ℝ)^4127 := by
      have hnat : (6250082924553869387 : ℕ)^1024*10000000000000000^4127 ≤ 10000032920501911^4127*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250082924553869387 6250000000000000000 10000032920501911 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032920501911/10000000000000000 : ℝ)) (X := (6250082924553869387/6250000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100179497389308781057/100000000000000000000 : ℝ) ≤ (62527817031827/62500000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (100179497389308781057/100000000000000000000 : ℝ)^1024 ≤ (62527817031827/62500000000000 : ℝ)^4127 := by
      have hnat : (100179497389308781057 : ℕ)^1024*62500000000000^4127 ≤ 62527817031827^4127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100179497389308781057 100000000000000000000 62527817031827 62500000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62527817031827/62500000000000 : ℝ)) (X := (100179497389308781057/100000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50178833992877825961/50000000000000000000 : ℝ) ≤ (10008868529682729/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50178833992877825961/50000000000000000000 : ℝ)^1024 ≤ (10008868529682729/10000000000000000 : ℝ)^4127 := by
      have hnat : (50178833992877825961 : ℕ)^1024*10000000000000000^4127 ≤ 10008868529682729^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50178833992877825961 50000000000000000000 10008868529682729 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008868529682729/10000000000000000 : ℝ)) (X := (50178833992877825961/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(82924553869387/12500000000000000000 : ℝ) ≤ ((390386643516478511/390500000000000000 : ℝ)+2*(4417804590409/1562000000000000 : ℝ)*(519/10000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (390386643516478511/390500000000000000 : ℝ)+2*(4417804590409/1562000000000000 : ℝ)*(519/10000 : ℝ)=(10000032920501911/10000000000000000 : ℝ) by norm_num, show 1+2*(82924553869387/12500000000000000000 : ℝ)=(6250082924553869387/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(178833992877825961/100000000000000000000 : ℝ)+(82924553869387/12500000000000000000 : ℝ) ≤ ((390386643516478511/390500000000000000 : ℝ)+(4417804590409/1562000000000000 : ℝ)*((2081/10000 : ℝ)+(519/10000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (390386643516478511/390500000000000000 : ℝ)+(4417804590409/1562000000000000 : ℝ)*((2081/10000 : ℝ)+(519/10000 : ℝ))=(62527817031827/62500000000000 : ℝ) by norm_num, show 1+(178833992877825961/100000000000000000000 : ℝ)+(82924553869387/12500000000000000000 : ℝ)=(100179497389308781057/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(178833992877825961/100000000000000000000 : ℝ) ≤ ((390386643516478511/390500000000000000 : ℝ)+2*(4417804590409/1562000000000000 : ℝ)*(2081/10000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (390386643516478511/390500000000000000 : ℝ)+2*(4417804590409/1562000000000000 : ℝ)*(2081/10000 : ℝ)=(10008868529682729/10000000000000000 : ℝ) by norm_num, show 1+2*(178833992877825961/100000000000000000000 : ℝ)=(50178833992877825961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (390386643516478511/390500000000000000 : ℝ)*(X 1 0+X 2 0)+(4417804590409/1562000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (519/10000 : ℝ)) (hi := (2081/10000 : ℝ)) (c := (390386643516478511/390500000000000000 : ℝ)) (alpha := (4417804590409/1562000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (390386643516478511/390500000000000000 : ℝ)*(X 0 1+X 2 1)+(4417804590409/1562000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (519/10000 : ℝ)) (hi := (2081/10000 : ℝ)) (c := (390386643516478511/390500000000000000 : ℝ)) (alpha := (4417804590409/1562000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (390386643516478511/390500000000000000 : ℝ)*(X 0 2+X 1 2)+(4417804590409/1562000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (519/10000 : ℝ)) (hi := (2081/10000 : ℝ)) (c := (390386643516478511/390500000000000000 : ℝ)) (alpha := (4417804590409/1562000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092728119/5000000000 : ℝ)*X 0 0+(5526731631/10000000000 : ℝ)*X 0 1+(5145219941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377382657/10000000000 : ℝ)*X 1 0+(-2384451251/10000000000 : ℝ)*X 1 1+(2572610659/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((168043213/312500000 : ℝ)*X 2 0+(1029044221/2000000000 : ℝ)*X 2 1+(-2384451317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363459773/10000000000 : ℝ)*X 0 0+(4006042951/10000000000 : ℝ)*X 0 1+(297071931/625000000 : ℝ)*X 0 2+(4363459773/10000000000 : ℝ)*X 1 0+(4006042951/10000000000 : ℝ)*X 1 1+(297071931/625000000 : ℝ)*X 1 2+(4363459773/10000000000 : ℝ)*X 2 0+(4006042951/10000000000 : ℝ)*X 2 1+(297071931/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1092791613/5000000000 : ℝ)*X 0 0+(2574002209/5000000000 : ℝ)*X 0 1+(5523918119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281112357/10000000000 : ℝ)*X 1 0+(-1002877763/5000000000 : ℝ)*X 1 1+(27619591/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5281112599/10000000000 : ℝ)*X 2 0+(1380979509/2500000000 : ℝ)*X 2 1+(-2005755421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181853669/5000000000 : ℝ)*X 0 0+(2373851719/5000000000 : ℝ)*X 0 1+(200577481/500000000 : ℝ)*X 0 2+(2181853669/5000000000 : ℝ)*X 1 0+(2373851719/5000000000 : ℝ)*X 1 1+(200577481/500000000 : ℝ)*X 1 2+(2181853669/5000000000 : ℝ)*X 2 0+(2373851719/5000000000 : ℝ)*X 2 1+(200577481/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24755805284535300684081/9762500000000000000000000000 : ℝ) := by norm_num
    linear_combination (57870629/25000000000000 : ℝ)*(base1) + (1245572801/50000000000000 : ℝ)*(base19) + (160540647/6250000000000 : ℝ)*(base23) + (249828779/100000000000000 : ℝ)*(upper3) + (228330683/100000000000000 : ℝ)*(upper5) + (494965845423481/25000000000000 : ℝ)*(major0) + (494965845423481/25000000000000 : ℝ)*(major1) + (494965845423481/25000000000000 : ℝ)*(major2) + (655295751652741/25000000000000 : ℝ)*(sp0) + (2621212008605219/100000000000000 : ℝ)*(sp1) + (262121193110047/10000000000000 : ℝ)*(sp2) + (669251545284203/50000000000000 : ℝ)*(sp3) + (31724622373/100000000000000 : ℝ)*(sp4) + (8857059237/100000000000000 : ℝ)*(sp7) + (669256089555079/50000000000000 : ℝ)*(f.failure) + (2621214499750821/100000000000000 : ℝ)*(f.sum) + (30998056284621/19525000000000000000000000000 : ℝ)*base66 + (21468071193374041/9762500000000000000000000000000 : ℝ)*base67 + (114313973598838459/9762500000000000000000000000000 : ℝ)*base70 + (26909779318661541/9762500000000000000000000000000 : ℝ)*base71 + (27970653503327/9762500000000000000000000000 : ℝ)*base73 + (24453569490225959/9762500000000000000000000000000 : ℝ)*base76 + (11527493350050959/9762500000000000000000000000000 : ℝ)*base78 + (5032188296974041/9762500000000000000000000000000 : ℝ)*base79 + (49058847481421/19525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2491751/5000000000000000000000 : ℝ)*base90 + (2491751/5000000000000000000000 : ℝ)*base92 + (2491751/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123592480664962286116257537/19525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (609287987/50000000000000 : ℝ)*(base19) + (35830561/2500000000000 : ℝ)*(base23) + (85549509/50000000000000 : ℝ)*(upper3) + (14889891/50000000000000 : ℝ)*(lower4) + (8391281/6250000000000 : ℝ)*(upper5) + (2009298534469711/100000000000000 : ℝ)*(major0) + (2009298534469711/100000000000000 : ℝ)*(major1) + (2009298534469711/100000000000000 : ℝ)*(major2) + (10454087969/100000000000000 : ℝ)*(sp1) + (12448586539/100000000000000 : ℝ)*(sp2) + (1330092332043907/50000000000000 : ℝ)*(sp4) + (20782601495499/781250000000 : ℝ)*(sp5) + (532034156455767/20000000000000 : ℝ)*(sp6) + (679206096926459/50000000000000 : ℝ)*(sp7) + (679206096926459/50000000000000 : ℝ)*(f.failure) + (1330092332043907/50000000000000 : ℝ)*(f.sum) + (181210155790201/78100000000000000000000000000 : ℝ)*base66 + (96093340591530071/39050000000000000000000000000000 : ℝ)*base67 + (42454311747030071/39050000000000000000000000000000 : ℝ)*base69 + (70156484817719929/39050000000000000000000000000000 : ℝ)*base72 + (4439543071501/78100000000000000000000000000 : ℝ)*base74 + (130915648200769929/39050000000000000000000000000000 : ℝ)*base76 + (122745983351680071/39050000000000000000000000000000 : ℝ)*base77 + (45042830304380071/39050000000000000000000000000000 : ℝ)*base79 + (329369795310401/78100000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (22997029/5000000000000000000000 : ℝ)*base89 + (22997029/5000000000000000000000 : ℝ)*base91 + (22997029/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1062_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2081/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1062_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1062_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1062_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1062_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2173/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8377/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:47:32.101361+00:00
-- url     : https://prove2.me/submissions/83ce2ce8-c9b1-4ea2-bc32-e09cee3974f0

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
theorem support_rectangle_w1041_s6_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216080041/10000000000 : ℝ)*x 0 + (2697715281/5000000000 : ℝ)*x 1 + (5263382333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216080041/10000000000 : ℝ)^4117 ≤ (13456382112571/100000000000000 : ℝ)^3093 := by
    have hnat : (2216080041 : ℕ)^4117*100000000000000^3093 ≤ 13456382112571^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216080041 10000000000 13456382112571 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697715281/5000000000 : ℝ)^4117 ≤ (43985339522763/100000000000000 : ℝ)^3093 := by
    have hnat : (2697715281 : ℕ)^4117*100000000000000^3093 ≤ 43985339522763^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697715281 5000000000 43985339522763 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263382333/10000000000 : ℝ)^4117 ≤ (21279139177087/50000000000000 : ℝ)^3093 := by
    have hnat : (5263382333 : ℕ)^4117*50000000000000^3093 ≤ 21279139177087^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263382333 10000000000 21279139177087 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216080041/10000000000 : ℝ), (2697715281/5000000000 : ℝ), (5263382333/10000000000 : ℝ)] ![(13456382112571/100000000000000 : ℝ), (43985339522763/100000000000000 : ℝ), (21279139177087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216080041/10000000000 : ℝ)|^4117 ≤ (13456382112571/100000000000000 : ℝ)^3093
        have hw : |(-2216080041/10000000000 : ℝ)|=(2216080041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697715281/5000000000 : ℝ)|^4117 ≤ (43985339522763/100000000000000 : ℝ)^3093
        have hw : |(2697715281/5000000000 : ℝ)|=(2697715281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263382333/10000000000 : ℝ)|^4117 ≤ (21279139177087/50000000000000 : ℝ)^3093
        have hw : |(5263382333/10000000000 : ℝ)|=(5263382333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345190859/10000000000 : ℝ)*x 0 + (-1141546647/5000000000 : ℝ)*x 1 + (65792279/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345190859/10000000000 : ℝ)^4117 ≤ (5430126777527/12500000000000 : ℝ)^3093 := by
    have hnat : (5345190859 : ℕ)^4117*12500000000000^3093 ≤ 5430126777527^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345190859 10000000000 5430126777527 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141546647/5000000000 : ℝ)^4117 ≤ (437522111273/3125000000000 : ℝ)^3093 := by
    have hnat : (1141546647 : ℕ)^4117*3125000000000^3093 ≤ 437522111273^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141546647 5000000000 437522111273 3125000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65792279/125000000 : ℝ)^4117 ≤ (2127913910713/5000000000000 : ℝ)^3093 := by
    have hnat : (65792279 : ℕ)^4117*5000000000000^3093 ≤ 2127913910713^3093*125000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65792279 125000000 2127913910713 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345190859/10000000000 : ℝ), (-1141546647/5000000000 : ℝ), (65792279/125000000 : ℝ)] ![(5430126777527/12500000000000 : ℝ), (437522111273/3125000000000 : ℝ), (2127913910713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345190859/10000000000 : ℝ)|^4117 ≤ (5430126777527/12500000000000 : ℝ)^3093
        have hw : |(5345190859/10000000000 : ℝ)|=(5345190859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141546647/5000000000 : ℝ)|^4117 ≤ (437522111273/3125000000000 : ℝ)^3093
        have hw : |(-1141546647/5000000000 : ℝ)|=(1141546647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65792279/125000000 : ℝ)|^4117 ≤ (2127913910713/5000000000000 : ℝ)^3093
        have hw : |(65792279/125000000 : ℝ)|=(65792279/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345190719/10000000000 : ℝ)*x 0 + (1052676483/2000000000 : ℝ)*x 1 + (-2283093353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345190719/10000000000 : ℝ)^4117 ≤ (43441012705729/100000000000000 : ℝ)^3093 := by
    have hnat : (5345190719 : ℕ)^4117*100000000000000^3093 ≤ 43441012705729^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345190719 10000000000 43441012705729 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052676483/2000000000 : ℝ)^4117 ≤ (42558279236713/100000000000000 : ℝ)^3093 := by
    have hnat : (1052676483 : ℕ)^4117*100000000000000^3093 ≤ 42558279236713^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052676483 2000000000 42558279236713 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283093353/10000000000 : ℝ)^4117 ≤ (1750088505291/12500000000000 : ℝ)^3093 := by
    have hnat : (2283093353 : ℕ)^4117*12500000000000^3093 ≤ 1750088505291^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283093353 10000000000 1750088505291 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345190719/10000000000 : ℝ), (1052676483/2000000000 : ℝ), (-2283093353/10000000000 : ℝ)] ![(43441012705729/100000000000000 : ℝ), (42558279236713/100000000000000 : ℝ), (1750088505291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345190719/10000000000 : ℝ)|^4117 ≤ (43441012705729/100000000000000 : ℝ)^3093
        have hw : |(5345190719/10000000000 : ℝ)|=(5345190719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052676483/2000000000 : ℝ)|^4117 ≤ (42558279236713/100000000000000 : ℝ)^3093
        have hw : |(1052676483/2000000000 : ℝ)|=(1052676483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283093353/10000000000 : ℝ)|^4117 ≤ (1750088505291/12500000000000 : ℝ)^3093
        have hw : |(-2283093353/10000000000 : ℝ)|=(2283093353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875813621/2000000000 : ℝ)*x 0 + (4152579/9765625 : ℝ)*x 1 + (901950689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875813621/2000000000 : ℝ)^4117 ≤ (33316078908017/100000000000000 : ℝ)^3093 := by
    have hnat : (875813621 : ℕ)^4117*100000000000000^3093 ≤ 33316078908017^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875813621 2000000000 33316078908017 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152579/9765625 : ℝ)^4117 ≤ (16018960128243/50000000000000 : ℝ)^3093 := by
    have hnat : (4152579 : ℕ)^4117*50000000000000^3093 ≤ 16018960128243^3093*9765625^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152579 9765625 16018960128243 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901950689/2000000000 : ℝ)^4117 ≤ (34646000823239/100000000000000 : ℝ)^3093 := by
    have hnat : (901950689 : ℕ)^4117*100000000000000^3093 ≤ 34646000823239^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901950689 2000000000 34646000823239 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875813621/2000000000 : ℝ), (4152579/9765625 : ℝ), (901950689/2000000000 : ℝ)] ![(33316078908017/100000000000000 : ℝ), (16018960128243/50000000000000 : ℝ), (34646000823239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875813621/2000000000 : ℝ)|^4117 ≤ (33316078908017/100000000000000 : ℝ)^3093
        have hw : |(875813621/2000000000 : ℝ)|=(875813621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152579/9765625 : ℝ)|^4117 ≤ (16018960128243/50000000000000 : ℝ)^3093
        have hw : |(4152579/9765625 : ℝ)|=(4152579/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901950689/2000000000 : ℝ)|^4117 ≤ (34646000823239/100000000000000 : ℝ)^3093
        have hw : |(901950689/2000000000 : ℝ)|=(901950689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216085369/10000000000 : ℝ)*x 0 + (2631857919/5000000000 : ℝ)*x 1 + (2697547903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216085369/10000000000 : ℝ)^4117 ≤ (336410629399/2500000000000 : ℝ)^3093 := by
    have hnat : (2216085369 : ℕ)^4117*2500000000000^3093 ≤ 336410629399^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216085369 10000000000 336410629399 2500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631857919/5000000000 : ℝ)^4117 ≤ (5320233474567/12500000000000 : ℝ)^3093 := by
    have hnat : (2631857919 : ℕ)^4117*12500000000000^3093 ≤ 5320233474567^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631857919 5000000000 5320233474567 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697547903/5000000000 : ℝ)^4117 ≤ (43981707013777/100000000000000 : ℝ)^3093 := by
    have hnat : (2697547903 : ℕ)^4117*100000000000000^3093 ≤ 43981707013777^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697547903 5000000000 43981707013777 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216085369/10000000000 : ℝ), (2631857919/5000000000 : ℝ), (2697547903/5000000000 : ℝ)] ![(336410629399/2500000000000 : ℝ), (5320233474567/12500000000000 : ℝ), (43981707013777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216085369/10000000000 : ℝ)|^4117 ≤ (336410629399/2500000000000 : ℝ)^3093
        have hw : |(-2216085369/10000000000 : ℝ)|=(2216085369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631857919/5000000000 : ℝ)|^4117 ≤ (5320233474567/12500000000000 : ℝ)^3093
        have hw : |(2631857919/5000000000 : ℝ)|=(2631857919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697547903/5000000000 : ℝ)|^4117 ≤ (43981707013777/100000000000000 : ℝ)^3093
        have hw : |(2697547903/5000000000 : ℝ)|=(2697547903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655998629/5000000000 : ℝ)*x 0 + (-2151379811/10000000000 : ℝ)*x 1 + (2697547951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655998629/5000000000 : ℝ)^4117 ≤ (43082303163833/100000000000000 : ℝ)^3093 := by
    have hnat : (2655998629 : ℕ)^4117*100000000000000^3093 ≤ 43082303163833^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655998629 5000000000 43082303163833 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151379811/10000000000 : ℝ)^4117 ≤ (3233997190973/25000000000000 : ℝ)^3093 := by
    have hnat : (2151379811 : ℕ)^4117*25000000000000^3093 ≤ 3233997190973^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151379811 10000000000 3233997190973 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697547951/5000000000 : ℝ)^4117 ≤ (43981708055483/100000000000000 : ℝ)^3093 := by
    have hnat : (2697547951 : ℕ)^4117*100000000000000^3093 ≤ 43981708055483^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697547951 5000000000 43981708055483 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655998629/5000000000 : ℝ), (-2151379811/10000000000 : ℝ), (2697547951/5000000000 : ℝ)] ![(43082303163833/100000000000000 : ℝ), (3233997190973/25000000000000 : ℝ), (43981708055483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655998629/5000000000 : ℝ)|^4117 ≤ (43082303163833/100000000000000 : ℝ)^3093
        have hw : |(2655998629/5000000000 : ℝ)|=(2655998629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151379811/10000000000 : ℝ)|^4117 ≤ (3233997190973/25000000000000 : ℝ)^3093
        have hw : |(-2151379811/10000000000 : ℝ)|=(2151379811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697547951/5000000000 : ℝ)|^4117 ≤ (43981708055483/100000000000000 : ℝ)^3093
        have hw : |(2697547951/5000000000 : ℝ)|=(2697547951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655998639/5000000000 : ℝ)*x 0 + (2697547911/5000000000 : ℝ)*x 1 + (-2151379893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655998639/5000000000 : ℝ)^4117 ≤ (21541151689871/50000000000000 : ℝ)^3093 := by
    have hnat : (2655998639 : ℕ)^4117*50000000000000^3093 ≤ 21541151689871^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655998639 5000000000 21541151689871 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697547911/5000000000 : ℝ)^4117 ≤ (21990853593697/50000000000000 : ℝ)^3093 := by
    have hnat : (2697547911 : ℕ)^4117*50000000000000^3093 ≤ 21990853593697^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697547911 5000000000 21990853593697 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151379893/10000000000 : ℝ)^4117 ≤ (1616998677523/12500000000000 : ℝ)^3093 := by
    have hnat : (2151379893 : ℕ)^4117*12500000000000^3093 ≤ 1616998677523^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151379893 10000000000 1616998677523 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655998639/5000000000 : ℝ), (2697547911/5000000000 : ℝ), (-2151379893/10000000000 : ℝ)] ![(21541151689871/50000000000000 : ℝ), (21990853593697/50000000000000 : ℝ), (1616998677523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655998639/5000000000 : ℝ)|^4117 ≤ (21541151689871/50000000000000 : ℝ)^3093
        have hw : |(2655998639/5000000000 : ℝ)|=(2655998639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697547911/5000000000 : ℝ)|^4117 ≤ (21990853593697/50000000000000 : ℝ)^3093
        have hw : |(2697547911/5000000000 : ℝ)|=(2697547911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151379893/10000000000 : ℝ)|^4117 ≤ (1616998677523/12500000000000 : ℝ)^3093
        have hw : |(-2151379893/10000000000 : ℝ)|=(2151379893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s6_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379078599/10000000000 : ℝ)*x 0 + (4509102671/10000000000 : ℝ)*x 1 + (531611729/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379078599/10000000000 : ℝ)^4117 ≤ (16658092589459/50000000000000 : ℝ)^3093 := by
    have hnat : (4379078599 : ℕ)^4117*50000000000000^3093 ≤ 16658092589459^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379078599 10000000000 16658092589459 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509102671/10000000000 : ℝ)^4117 ≤ (34639346236683/100000000000000 : ℝ)^3093 := by
    have hnat : (4509102671 : ℕ)^4117*100000000000000^3093 ≤ 34639346236683^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509102671 10000000000 34639346236683 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531611729/1250000000 : ℝ)^4117 ≤ (16022234281923/50000000000000 : ℝ)^3093 := by
    have hnat : (531611729 : ℕ)^4117*50000000000000^3093 ≤ 16022234281923^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531611729 1250000000 16022234281923 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379078599/10000000000 : ℝ), (4509102671/10000000000 : ℝ), (531611729/1250000000 : ℝ)] ![(16658092589459/50000000000000 : ℝ), (34639346236683/100000000000000 : ℝ), (16022234281923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379078599/10000000000 : ℝ)|^4117 ≤ (16658092589459/50000000000000 : ℝ)^3093
        have hw : |(4379078599/10000000000 : ℝ)|=(4379078599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509102671/10000000000 : ℝ)|^4117 ≤ (34639346236683/100000000000000 : ℝ)^3093
        have hw : |(4509102671/10000000000 : ℝ)|=(4509102671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531611729/1250000000 : ℝ)|^4117 ≤ (16022234281923/50000000000000 : ℝ)^3093
        have hw : |(531611729/1250000000 : ℝ)|=(531611729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2801/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5579/50000 : ℝ) ^ (8233/2048 : ℝ) ≤ (14834692674544589/100000000000000000000 : ℝ) := by
    have hpowers : (5579/50000 : ℝ)^8233 ≤ (14834692674544589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5579 : ℕ)^8233*100000000000000000000^2048 ≤ 14834692674544589^2048*50000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5579 50000 14834692674544589 100000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5579/50000 : ℝ)) (X := (14834692674544589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (9363924844868429/25000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^8233 ≤ (9363924844868429/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14049 : ℕ)^8233*25000000000000000000^2048 ≤ 9363924844868429^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 9363924844868429 25000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (9363924844868429/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014834692674544589/50000000000000000000 : ℝ) ≤ (10000737958589251/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (50014834692674544589/50000000000000000000 : ℝ)^2048 ≤ (10000737958589251/10000000000000000 : ℝ)^8233 := by
      have hnat : (50014834692674544589 : ℕ)^2048*10000000000000000^8233 ≤ 10000737958589251^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014834692674544589 50000000000000000000 10000737958589251 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000737958589251/10000000000000000 : ℝ)) (X := (50014834692674544589/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010458078410803661/20000000000000000000 : ℝ) ≤ (5000650247146707/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (20010458078410803661/20000000000000000000 : ℝ)^2048 ≤ (5000650247146707/5000000000000000 : ℝ)^8233 := by
      have hnat : (20010458078410803661 : ℕ)^2048*5000000000000000^8233 ≤ 5000650247146707^8233*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010458078410803661 20000000000000000000 5000650247146707 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000650247146707/5000000000000000 : ℝ)) (X := (20010458078410803661/20000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509363924844868429/12500000000000000000 : ℝ) ≤ (10001863029997577/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (12509363924844868429/12500000000000000000 : ℝ)^2048 ≤ (10001863029997577/10000000000000000 : ℝ)^8233 := by
      have hnat : (12509363924844868429 : ℕ)^2048*10000000000000000^8233 ≤ 10001863029997577^8233*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509363924844868429 12500000000000000000 10001863029997577 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001863029997577/10000000000000000 : ℝ)) (X := (12509363924844868429/12500000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14834692674544589/100000000000000000000 : ℝ) ≤ ((4128511413072489019/4130000000000000000 : ℝ)+2*(562535704163/289100000000000 : ℝ)*(5579/50000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (4128511413072489019/4130000000000000000 : ℝ)+2*(562535704163/289100000000000 : ℝ)*(5579/50000 : ℝ)=(10000737958589251/10000000000000000 : ℝ) by norm_num, show 1+2*(14834692674544589/100000000000000000000 : ℝ)=(50014834692674544589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9363924844868429/25000000000000000000 : ℝ)+(14834692674544589/100000000000000000000 : ℝ) ≤ ((4128511413072489019/4130000000000000000 : ℝ)+(562535704163/289100000000000 : ℝ)*((14049/100000 : ℝ)+(5579/50000 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (4128511413072489019/4130000000000000000 : ℝ)+(562535704163/289100000000000 : ℝ)*((14049/100000 : ℝ)+(5579/50000 : ℝ))=(5000650247146707/5000000000000000 : ℝ) by norm_num, show 1+(9363924844868429/25000000000000000000 : ℝ)+(14834692674544589/100000000000000000000 : ℝ)=(20010458078410803661/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9363924844868429/25000000000000000000 : ℝ) ≤ ((4128511413072489019/4130000000000000000 : ℝ)+2*(562535704163/289100000000000 : ℝ)*(14049/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (4128511413072489019/4130000000000000000 : ℝ)+2*(562535704163/289100000000000 : ℝ)*(14049/100000 : ℝ)=(10001863029997577/10000000000000000 : ℝ) by norm_num, show 1+2*(9363924844868429/25000000000000000000 : ℝ)=(12509363924844868429/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4128511413072489019/4130000000000000000 : ℝ)*(X 1 0+X 2 0)+(562535704163/289100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (4128511413072489019/4130000000000000000 : ℝ)) (alpha := (562535704163/289100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4128511413072489019/4130000000000000000 : ℝ)*(X 0 1+X 2 1)+(562535704163/289100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (4128511413072489019/4130000000000000000 : ℝ)) (alpha := (562535704163/289100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4128511413072489019/4130000000000000000 : ℝ)*(X 0 2+X 1 2)+(562535704163/289100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (4128511413072489019/4130000000000000000 : ℝ)) (alpha := (562535704163/289100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2216080041/10000000000 : ℝ)*X 0 0+(2697715281/5000000000 : ℝ)*X 0 1+(5263382333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345190859/10000000000 : ℝ)*X 1 0+(-1141546647/5000000000 : ℝ)*X 1 1+(65792279/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345190719/10000000000 : ℝ)*X 2 0+(1052676483/2000000000 : ℝ)*X 2 1+(-2283093353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875813621/2000000000 : ℝ)*X 0 0+(4152579/9765625 : ℝ)*X 0 1+(901950689/2000000000 : ℝ)*X 0 2+(875813621/2000000000 : ℝ)*X 1 0+(4152579/9765625 : ℝ)*X 1 1+(901950689/2000000000 : ℝ)*X 1 2+(875813621/2000000000 : ℝ)*X 2 0+(4152579/9765625 : ℝ)*X 2 1+(901950689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216085369/10000000000 : ℝ)*X 0 0+(2631857919/5000000000 : ℝ)*X 0 1+(2697547903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655998629/5000000000 : ℝ)*X 1 0+(-2151379811/10000000000 : ℝ)*X 1 1+(2697547951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655998639/5000000000 : ℝ)*X 2 0+(2697547911/5000000000 : ℝ)*X 2 1+(-2151379893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379078599/10000000000 : ℝ)*X 0 0+(4509102671/10000000000 : ℝ)*X 0 1+(531611729/1250000000 : ℝ)*X 0 2+(4379078599/10000000000 : ℝ)*X 1 0+(4509102671/10000000000 : ℝ)*X 1 1+(531611729/1250000000 : ℝ)*X 1 2+(4379078599/10000000000 : ℝ)*X 2 0+(4509102671/10000000000 : ℝ)*X 2 1+(531611729/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45786852681535216190241/14455000000000000000000000000 : ℝ) := by norm_num
    linear_combination (366681823/50000000000000 : ℝ)*(base19) + (263400487/50000000000000 : ℝ)*(base23) + (1097327/25000000000000 : ℝ)*(lower2) + (36639551/25000000000000 : ℝ)*(upper3) + (10145171/100000000000000 : ℝ)*(upper5) + (5728177781124537/100000000000000 : ℝ)*(major0) + (5728177781124537/100000000000000 : ℝ)*(major1) + (5728177781124537/100000000000000 : ℝ)*(major2) + (7573013417363377/100000000000000 : ℝ)*(sp0) + (757302718237851/10000000000000 : ℝ)*(sp1) + (3786513694470591/50000000000000 : ℝ)*(sp2) + (1941657911852909/50000000000000 : ℝ)*(sp3) + (724918939/5000000000000 : ℝ)*(sp4) + (292930407/2500000000000 : ℝ)*(sp7) + (3883327540922099/100000000000000 : ℝ)*(f.failure) + (1893256978935539/25000000000000 : ℝ)*(f.sum) + (2081630090251/903437500000000000000000000 : ℝ)*base65 + (6636966870321185579/2891000000000000000000000000000000 : ℝ)*base68 + (61536712462600185579/2891000000000000000000000000000000 : ℝ)*base70 + (8302262972880814421/2891000000000000000000000000000000 : ℝ)*base71 + (57334533480591/14455000000000000000000000000 : ℝ)*base73 + (7652889849889185579/2891000000000000000000000000000000 : ℝ)*base76 + (32201437893592814421/2891000000000000000000000000000000 : ℝ)*base77 + (58486656004422814421/2891000000000000000000000000000000 : ℝ)*base79 + (10685937762111/14455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (64019/9765625000000000000 : ℝ)*base89 + (64019/9765625000000000000 : ℝ)*base91 + (64019/9765625000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39817481814885799169356209/4130000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1001880923/50000000000000 : ℝ)*(base19) + (1088858941/50000000000000 : ℝ)*(base23) + (207875727/100000000000000 : ℝ)*(upper3) + (92566703/100000000000000 : ℝ)*(lower4) + (165589213/50000000000000 : ℝ)*(upper5) + (115145766145663/2000000000000 : ℝ)*(major0) + (115145766145663/2000000000000 : ℝ)*(major1) + (115145766145663/2000000000000 : ℝ)*(major2) + (5981979277/10000000000000 : ℝ)*(sp1) + (55185331509/100000000000000 : ℝ)*(sp2) + (3805756865711451/50000000000000 : ℝ)*(sp4) + (3805725953934143/50000000000000 : ℝ)*(sp5) + (7611456368373511/100000000000000 : ℝ)*(sp6) + (1951531280887749/50000000000000 : ℝ)*(sp7) + (1951531280887749/50000000000000 : ℝ)*(f.failure) + (3805756865711451/50000000000000 : ℝ)*(f.sum) + (3016996988367/1445500000000000000000000000 : ℝ)*base66 + (704042064054842179/57820000000000000000000000000000 : ℝ)*base67 + (84194299899362179/57820000000000000000000000000000 : ℝ)*base69 + (155431391025677821/57820000000000000000000000000000 : ℝ)*base72 + (2375801604689/1445500000000000000000000000 : ℝ)*base73 + (149609043535837821/57820000000000000000000000000000 : ℝ)*base76 + (582992523322302179/57820000000000000000000000000000 : ℝ)*base77 + (414117354209022179/57820000000000000000000000000000 : ℝ)*base79 + (3557191717343/1445500000000000000000000000 : ℝ)*base82 + (37081/4882812500000000000 : ℝ)*base90 + (37081/4882812500000000000 : ℝ)*base92 + (37081/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1041_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_s7_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-277015667/1250000000 : ℝ)*x 0 + (5394909561/10000000000 : ℝ)*x 1 + (2631936797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277015667/1250000000 : ℝ)^4117 ≤ (1682093526131/12500000000000 : ℝ)^3093 := by
    have hnat : (277015667 : ℕ)^4117*12500000000000^3093 ≤ 1682093526131^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277015667 1250000000 1682093526131 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394909561/10000000000 : ℝ)^4117 ≤ (5497460757717/12500000000000 : ℝ)^3093 := by
    have hnat : (5394909561 : ℕ)^4117*12500000000000^3093 ≤ 5497460757717^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394909561 10000000000 5497460757717 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631936797/5000000000 : ℝ)^4117 ≤ (532044571457/1250000000000 : ℝ)^3093 := by
    have hnat : (2631936797 : ℕ)^4117*1250000000000^3093 ≤ 532044571457^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631936797 5000000000 532044571457 1250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277015667/1250000000 : ℝ), (5394909561/10000000000 : ℝ), (2631936797/5000000000 : ℝ)] ![(1682093526131/12500000000000 : ℝ), (5497460757717/12500000000000 : ℝ), (532044571457/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277015667/1250000000 : ℝ)|^4117 ≤ (1682093526131/12500000000000 : ℝ)^3093
        have hw : |(-277015667/1250000000 : ℝ)|=(277015667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394909561/10000000000 : ℝ)|^4117 ≤ (5497460757717/12500000000000 : ℝ)^3093
        have hw : |(5394909561/10000000000 : ℝ)|=(5394909561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631936797/5000000000 : ℝ)|^4117 ≤ (532044571457/1250000000000 : ℝ)^3093
        have hw : |(2631936797/5000000000 : ℝ)|=(2631936797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672530559/5000000000 : ℝ)*x 0 + (-2282617163/10000000000 : ℝ)*x 1 + (5263873809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672530559/5000000000 : ℝ)^4117 ≤ (43439610717743/100000000000000 : ℝ)^3093 := by
    have hnat : (2672530559 : ℕ)^4117*100000000000000^3093 ≤ 43439610717743^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672530559 5000000000 43439610717743 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282617163/10000000000 : ℝ)^4117 ≤ (6998410619561/50000000000000 : ℝ)^3093 := by
    have hnat : (2282617163 : ℕ)^4117*50000000000000^3093 ≤ 6998410619561^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282617163 10000000000 6998410619561 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263873809/10000000000 : ℝ)^4117 ≤ (21281784015303/50000000000000 : ℝ)^3093 := by
    have hnat : (5263873809 : ℕ)^4117*50000000000000^3093 ≤ 21281784015303^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263873809 10000000000 21281784015303 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672530559/5000000000 : ℝ), (-2282617163/10000000000 : ℝ), (5263873809/10000000000 : ℝ)] ![(43439610717743/100000000000000 : ℝ), (6998410619561/50000000000000 : ℝ), (21281784015303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672530559/5000000000 : ℝ)|^4117 ≤ (43439610717743/100000000000000 : ℝ)^3093
        have hw : |(2672530559/5000000000 : ℝ)|=(2672530559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282617163/10000000000 : ℝ)|^4117 ≤ (6998410619561/50000000000000 : ℝ)^3093
        have hw : |(-2282617163/10000000000 : ℝ)|=(2282617163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263873809/10000000000 : ℝ)|^4117 ≤ (21281784015303/50000000000000 : ℝ)^3093
        have hw : |(5263873809/10000000000 : ℝ)|=(5263873809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345061209/10000000000 : ℝ)*x 0 + (5263873661/10000000000 : ℝ)*x 1 + (-570654309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345061209/10000000000 : ℝ)^4117 ≤ (5429951462769/12500000000000 : ℝ)^3093 := by
    have hnat : (5345061209 : ℕ)^4117*12500000000000^3093 ≤ 5429951462769^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345061209 10000000000 5429951462769 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263873661/10000000000 : ℝ)^4117 ≤ (42563566437681/100000000000000 : ℝ)^3093 := by
    have hnat : (5263873661 : ℕ)^4117*100000000000000^3093 ≤ 42563566437681^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263873661 10000000000 42563566437681 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570654309/2500000000 : ℝ)^4117 ≤ (13996821834949/100000000000000 : ℝ)^3093 := by
    have hnat : (570654309 : ℕ)^4117*100000000000000^3093 ≤ 13996821834949^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570654309 2500000000 13996821834949 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345061209/10000000000 : ℝ), (5263873661/10000000000 : ℝ), (-570654309/2500000000 : ℝ)] ![(5429951462769/12500000000000 : ℝ), (42563566437681/100000000000000 : ℝ), (13996821834949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345061209/10000000000 : ℝ)|^4117 ≤ (5429951462769/12500000000000 : ℝ)^3093
        have hw : |(5345061209/10000000000 : ℝ)|=(5345061209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263873661/10000000000 : ℝ)|^4117 ≤ (42563566437681/100000000000000 : ℝ)^3093
        have hw : |(5263873661/10000000000 : ℝ)|=(5263873661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-570654309/2500000000 : ℝ)|^4117 ≤ (13996821834949/100000000000000 : ℝ)^3093
        have hw : |(-570654309/2500000000 : ℝ)|=(570654309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379094173/10000000000 : ℝ)*x 0 + (4253224741/10000000000 : ℝ)*x 1 + (2254381339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379094173/10000000000 : ℝ)^4117 ≤ (6663268578849/20000000000000 : ℝ)^3093 := by
    have hnat : (4379094173 : ℕ)^4117*20000000000000^3093 ≤ 6663268578849^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379094173 10000000000 6663268578849 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253224741/10000000000 : ℝ)^4117 ≤ (32047787383489/100000000000000 : ℝ)^3093 := by
    have hnat : (4253224741 : ℕ)^4117*100000000000000^3093 ≤ 32047787383489^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253224741 10000000000 32047787383489 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254381339/5000000000 : ℝ)^4117 ≤ (4329483714253/12500000000000 : ℝ)^3093 := by
    have hnat : (2254381339 : ℕ)^4117*12500000000000^3093 ≤ 4329483714253^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254381339 5000000000 4329483714253 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379094173/10000000000 : ℝ), (4253224741/10000000000 : ℝ), (2254381339/5000000000 : ℝ)] ![(6663268578849/20000000000000 : ℝ), (32047787383489/100000000000000 : ℝ), (4329483714253/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379094173/10000000000 : ℝ)|^4117 ≤ (6663268578849/20000000000000 : ℝ)^3093
        have hw : |(4379094173/10000000000 : ℝ)|=(4379094173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253224741/10000000000 : ℝ)|^4117 ≤ (32047787383489/100000000000000 : ℝ)^3093
        have hw : |(4253224741/10000000000 : ℝ)|=(4253224741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254381339/5000000000 : ℝ)|^4117 ≤ (4329483714253/12500000000000 : ℝ)^3093
        have hw : |(2254381339/5000000000 : ℝ)|=(2254381339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108065187/5000000000 : ℝ)*x 0 + (658025277/1250000000 : ℝ)*x 1 + (1348644961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108065187/5000000000 : ℝ)^4117 ≤ (3364197232199/25000000000000 : ℝ)^3093 := by
    have hnat : (1108065187 : ℕ)^4117*25000000000000^3093 ≤ 3364197232199^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108065187 5000000000 3364197232199 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658025277/1250000000 : ℝ)^4117 ≤ (10641775678247/25000000000000 : ℝ)^3093 := by
    have hnat : (658025277 : ℕ)^4117*25000000000000^3093 ≤ 10641775678247^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658025277 1250000000 10641775678247 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348644961/2500000000 : ℝ)^4117 ≤ (10994027086463/25000000000000 : ℝ)^3093 := by
    have hnat : (1348644961 : ℕ)^4117*25000000000000^3093 ≤ 10994027086463^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348644961 2500000000 10994027086463 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108065187/5000000000 : ℝ), (658025277/1250000000 : ℝ), (1348644961/2500000000 : ℝ)] ![(3364197232199/25000000000000 : ℝ), (10641775678247/25000000000000 : ℝ), (10994027086463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108065187/5000000000 : ℝ)|^4117 ≤ (3364197232199/25000000000000 : ℝ)^3093
        have hw : |(-1108065187/5000000000 : ℝ)|=(1108065187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658025277/1250000000 : ℝ)|^4117 ≤ (10641775678247/25000000000000 : ℝ)^3093
        have hw : |(658025277/1250000000 : ℝ)|=(658025277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348644961/2500000000 : ℝ)|^4117 ≤ (10994027086463/25000000000000 : ℝ)^3093
        have hw : |(1348644961/2500000000 : ℝ)|=(1348644961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332007629/625000000 : ℝ)*x 0 + (-215191109/1000000000 : ℝ)*x 1 + (107891597/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332007629/625000000 : ℝ)^4117 ≤ (2692728156871/6250000000000 : ℝ)^3093 := by
    have hnat : (332007629 : ℕ)^4117*6250000000000^3093 ≤ 2692728156871^3093*625000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332007629 625000000 2692728156871 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215191109/1000000000 : ℝ)^4117 ≤ (6470120531913/50000000000000 : ℝ)^3093 := by
    have hnat : (215191109 : ℕ)^4117*50000000000000^3093 ≤ 6470120531913^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215191109 1000000000 6470120531913 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107891597/200000000 : ℝ)^4117 ≤ (10994027102739/25000000000000 : ℝ)^3093 := by
    have hnat : (107891597 : ℕ)^4117*25000000000000^3093 ≤ 10994027102739^3093*200000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107891597 200000000 10994027102739 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332007629/625000000 : ℝ), (-215191109/1000000000 : ℝ), (107891597/200000000 : ℝ)] ![(2692728156871/6250000000000 : ℝ), (6470120531913/50000000000000 : ℝ), (10994027102739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332007629/625000000 : ℝ)|^4117 ≤ (2692728156871/6250000000000 : ℝ)^3093
        have hw : |(332007629/625000000 : ℝ)|=(332007629/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215191109/1000000000 : ℝ)|^4117 ≤ (6470120531913/50000000000000 : ℝ)^3093
        have hw : |(-215191109/1000000000 : ℝ)|=(215191109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107891597/200000000 : ℝ)|^4117 ≤ (10994027102739/25000000000000 : ℝ)^3093
        have hw : |(107891597/200000000 : ℝ)|=(107891597/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656061031/5000000000 : ℝ)*x 0 + (2697289921/5000000000 : ℝ)*x 1 + (-430382221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656061031/5000000000 : ℝ)^4117 ≤ (8616730097669/20000000000000 : ℝ)^3093 := by
    have hnat : (2656061031 : ℕ)^4117*20000000000000^3093 ≤ 8616730097669^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656061031 5000000000 8616730097669 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697289921/5000000000 : ℝ)^4117 ≤ (879522166483/2000000000000 : ℝ)^3093 := by
    have hnat : (2697289921 : ℕ)^4117*2000000000000^3093 ≤ 879522166483^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697289921 5000000000 879522166483 2000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430382221/2000000000 : ℝ)^4117 ≤ (12940241183889/100000000000000 : ℝ)^3093 := by
    have hnat : (430382221 : ℕ)^4117*100000000000000^3093 ≤ 12940241183889^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430382221 2000000000 12940241183889 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656061031/5000000000 : ℝ), (2697289921/5000000000 : ℝ), (-430382221/2000000000 : ℝ)] ![(8616730097669/20000000000000 : ℝ), (879522166483/2000000000000 : ℝ), (12940241183889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656061031/5000000000 : ℝ)|^4117 ≤ (8616730097669/20000000000000 : ℝ)^3093
        have hw : |(2656061031/5000000000 : ℝ)|=(2656061031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697289921/5000000000 : ℝ)|^4117 ≤ (879522166483/2000000000000 : ℝ)^3093
        have hw : |(2697289921/5000000000 : ℝ)|=(2697289921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430382221/2000000000 : ℝ)|^4117 ≤ (12940241183889/100000000000000 : ℝ)^3093
        have hw : |(-430382221/2000000000 : ℝ)|=(430382221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s7_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2189552083/5000000000 : ℝ)*x 0 + (1127030531/2500000000 : ℝ)*x 1 + (4253867667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189552083/5000000000 : ℝ)^4117 ≤ (8329111022951/25000000000000 : ℝ)^3093 := by
    have hnat : (2189552083 : ℕ)^4117*25000000000000^3093 ≤ 8329111022951^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189552083 5000000000 8329111022951 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127030531/2500000000 : ℝ)^4117 ≤ (34629320107629/100000000000000 : ℝ)^3093 := by
    have hnat : (1127030531 : ℕ)^4117*100000000000000^3093 ≤ 34629320107629^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127030531 2500000000 34629320107629 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253867667/10000000000 : ℝ)^4117 ≤ (16027117895847/50000000000000 : ℝ)^3093 := by
    have hnat : (4253867667 : ℕ)^4117*50000000000000^3093 ≤ 16027117895847^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253867667 10000000000 16027117895847 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189552083/5000000000 : ℝ), (1127030531/2500000000 : ℝ), (4253867667/10000000000 : ℝ)] ![(8329111022951/25000000000000 : ℝ), (34629320107629/100000000000000 : ℝ), (16027117895847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189552083/5000000000 : ℝ)|^4117 ≤ (8329111022951/25000000000000 : ℝ)^3093
        have hw : |(2189552083/5000000000 : ℝ)|=(2189552083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127030531/2500000000 : ℝ)|^4117 ≤ (34629320107629/100000000000000 : ℝ)^3093
        have hw : |(1127030531/2500000000 : ℝ)|=(1127030531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253867667/10000000000 : ℝ)|^4117 ≤ (16027117895847/50000000000000 : ℝ)^3093
        have hw : |(4253867667/10000000000 : ℝ)|=(4253867667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1399/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2801/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2801/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2801/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2801/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2801/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2801/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2801/25000 : ℝ) ^ (8233/2048 : ℝ) ≤ (3770520482607033/25000000000000000000 : ℝ) := by
    have hpowers : (2801/25000 : ℝ)^8233 ≤ (3770520482607033/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2801 : ℕ)^8233*25000000000000000000^2048 ≤ 3770520482607033^2048*25000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 25000 3770520482607033 25000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/25000 : ℝ)) (X := (3770520482607033/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14001/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (36943898887925359/100000000000000000000 : ℝ) := by
    have hpowers : (14001/100000 : ℝ)^8233 ≤ (36943898887925359/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14001 : ℕ)^8233*100000000000000000000^2048 ≤ 36943898887925359^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14001 100000 36943898887925359 100000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14001/100000 : ℝ)) (X := (36943898887925359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503770520482607033/12500000000000000000 : ℝ) ≤ (625046891480449/625000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (12503770520482607033/12500000000000000000 : ℝ)^2048 ≤ (625046891480449/625000000000000 : ℝ)^8233 := by
      have hnat : (12503770520482607033 : ℕ)^2048*625000000000000^8233 ≤ 625046891480449^8233*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503770520482607033 12500000000000000000 625046891480449 625000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625046891480449/625000000000000 : ℝ)) (X := (12503770520482607033/12500000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052025980818353491/100000000000000000000 : ℝ) ≤ (10001293919507517/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (100052025980818353491/100000000000000000000 : ℝ)^2048 ≤ (10001293919507517/10000000000000000 : ℝ)^8233 := by
      have hnat : (100052025980818353491 : ℕ)^2048*10000000000000000^8233 ≤ 10001293919507517^8233*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052025980818353491 100000000000000000000 10001293919507517 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001293919507517/10000000000000000 : ℝ)) (X := (100052025980818353491/100000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036943898887925359/50000000000000000000 : ℝ) ≤ (200036751506557/200000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (50036943898887925359/50000000000000000000 : ℝ)^2048 ≤ (200036751506557/200000000000000 : ℝ)^8233 := by
      have hnat : (50036943898887925359 : ℕ)^2048*200000000000000^8233 ≤ 200036751506557^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036943898887925359 50000000000000000000 200036751506557 200000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200036751506557/200000000000000 : ℝ)) (X := (50036943898887925359/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3770520482607033/25000000000000000000 : ℝ) ≤ ((3494989530988878973/3496250000000000000 : ℝ)+2*(543655820333/279700000000000 : ℝ)*(2801/25000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (3494989530988878973/3496250000000000000 : ℝ)+2*(543655820333/279700000000000 : ℝ)*(2801/25000 : ℝ)=(625046891480449/625000000000000 : ℝ) by norm_num, show 1+2*(3770520482607033/25000000000000000000 : ℝ)=(12503770520482607033/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36943898887925359/100000000000000000000 : ℝ)+(3770520482607033/25000000000000000000 : ℝ) ≤ ((3494989530988878973/3496250000000000000 : ℝ)+(543655820333/279700000000000 : ℝ)*((14001/100000 : ℝ)+(2801/25000 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (3494989530988878973/3496250000000000000 : ℝ)+(543655820333/279700000000000 : ℝ)*((14001/100000 : ℝ)+(2801/25000 : ℝ))=(10001293919507517/10000000000000000 : ℝ) by norm_num, show 1+(36943898887925359/100000000000000000000 : ℝ)+(3770520482607033/25000000000000000000 : ℝ)=(100052025980818353491/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36943898887925359/100000000000000000000 : ℝ) ≤ ((3494989530988878973/3496250000000000000 : ℝ)+2*(543655820333/279700000000000 : ℝ)*(14001/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (3494989530988878973/3496250000000000000 : ℝ)+2*(543655820333/279700000000000 : ℝ)*(14001/100000 : ℝ)=(200036751506557/200000000000000 : ℝ) by norm_num, show 1+2*(36943898887925359/100000000000000000000 : ℝ)=(50036943898887925359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3494989530988878973/3496250000000000000 : ℝ)*(X 1 0+X 2 0)+(543655820333/279700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (2801/25000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (3494989530988878973/3496250000000000000 : ℝ)) (alpha := (543655820333/279700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3494989530988878973/3496250000000000000 : ℝ)*(X 0 1+X 2 1)+(543655820333/279700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (2801/25000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (3494989530988878973/3496250000000000000 : ℝ)) (alpha := (543655820333/279700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3494989530988878973/3496250000000000000 : ℝ)*(X 0 2+X 1 2)+(543655820333/279700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (2801/25000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (3494989530988878973/3496250000000000000 : ℝ)) (alpha := (543655820333/279700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-277015667/1250000000 : ℝ)*X 0 0+(5394909561/10000000000 : ℝ)*X 0 1+(2631936797/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672530559/5000000000 : ℝ)*X 1 0+(-2282617163/10000000000 : ℝ)*X 1 1+(5263873809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345061209/10000000000 : ℝ)*X 2 0+(5263873661/10000000000 : ℝ)*X 2 1+(-570654309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379094173/10000000000 : ℝ)*X 0 0+(4253224741/10000000000 : ℝ)*X 0 1+(2254381339/5000000000 : ℝ)*X 0 2+(4379094173/10000000000 : ℝ)*X 1 0+(4253224741/10000000000 : ℝ)*X 1 1+(2254381339/5000000000 : ℝ)*X 1 2+(4379094173/10000000000 : ℝ)*X 2 0+(4253224741/10000000000 : ℝ)*X 2 1+(2254381339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1108065187/5000000000 : ℝ)*X 0 0+(658025277/1250000000 : ℝ)*X 0 1+(1348644961/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332007629/625000000 : ℝ)*X 1 0+(-215191109/1000000000 : ℝ)*X 1 1+(107891597/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656061031/5000000000 : ℝ)*X 2 0+(2697289921/5000000000 : ℝ)*X 2 1+(-430382221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189552083/5000000000 : ℝ)*X 0 0+(1127030531/2500000000 : ℝ)*X 0 1+(4253867667/10000000000 : ℝ)*X 0 2+(2189552083/5000000000 : ℝ)*X 1 0+(1127030531/2500000000 : ℝ)*X 1 1+(4253867667/10000000000 : ℝ)*X 1 2+(2189552083/5000000000 : ℝ)*X 2 0+(1127030531/2500000000 : ℝ)*X 2 1+(4253867667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (592809694095751773046545621/87406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1593748723/100000000000000 : ℝ)*(base19) + (1695746229/100000000000000 : ℝ)*(base23) + (63162463/25000000000000 : ℝ)*(upper3) + (14929233/100000000000000 : ℝ)*(upper4) + (142208341/100000000000000 : ℝ)*(upper5) + (5772479580627159/100000000000000 : ℝ)*(major0) + (5772479580627159/100000000000000 : ℝ)*(major1) + (5772479580627159/100000000000000 : ℝ)*(major2) + (1907886679218403/25000000000000 : ℝ)*(sp0) + (7631596096127851/100000000000000 : ℝ)*(sp1) + (1526319198826069/20000000000000 : ℝ)*(sp2) + (1956667833631467/50000000000000 : ℝ)*(sp3) + (25486501481/50000000000000 : ℝ)*(sp4) + (25578040311/100000000000000 : ℝ)*(sp7) + (978340311325811/25000000000000 : ℝ)*(f.failure) + (3815798844938287/50000000000000 : ℝ)*(f.sum) + (84712718041233/13985000000000000000000000000 : ℝ)*base66 + (8393803760669584793/349625000000000000000000000000000 : ℝ)*base68 + (7652124096833459793/349625000000000000000000000000000 : ℝ)*base70 + (2208992696878084793/349625000000000000000000000000000 : ℝ)*base72 + (55488037373439/6992500000000000000000000000 : ℝ)*base74 + (1986330352257334793/349625000000000000000000000000000 : ℝ)*base76 + (2912539478695459793/349625000000000000000000000000000 : ℝ)*base78 + (7163119007575790207/349625000000000000000000000000000 : ℝ)*base79 + (44305570706509/6992500000000000000000000000 : ℝ)*base82 + (94819/39062500000000000000 : ℝ)*base90 + (94819/39062500000000000000 : ℝ)*base92 + (94819/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164766507820172554749547059/17481250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (442967479/25000000000000 : ℝ)*(base19) + (479059279/25000000000000 : ℝ)*(base23) + (11657727/6250000000000 : ℝ)*(upper3) + (1408453/2000000000000 : ℝ)*(lower4) + (198285243/100000000000000 : ℝ)*(upper5) + (1160309334098811/20000000000000 : ℝ)*(major0) + (1160309334098811/20000000000000 : ℝ)*(major1) + (1160309334098811/20000000000000 : ℝ)*(major2) + (48513360201/100000000000000 : ℝ)*(sp1) + (3180095111/6250000000000 : ℝ)*(sp2) + (3835013103800469/50000000000000 : ℝ)*(sp4) + (7669975922370821/100000000000000 : ℝ)*(sp5) + (3834986704921023/50000000000000 : ℝ)*(sp6) + (196653340960479/5000000000000 : ℝ)*(sp7) + (196653340960479/5000000000000 : ℝ)*(f.failure) + (3835013103800469/50000000000000 : ℝ)*(f.sum) + (5970592327933/2797000000000000000000000000 : ℝ)*base66 + (417262707317411397/69925000000000000000000000000000 : ℝ)*base68 + (111802638677888603/69925000000000000000000000000000 : ℝ)*base69 + (517391322571361397/69925000000000000000000000000000 : ℝ)*base72 + (948555239533/349625000000000000000000000 : ℝ)*base73 + (174270241003086397/69925000000000000000000000000000 : ℝ)*base76 + (304857555743311397/69925000000000000000000000000000 : ℝ)*base78 + (1128868459012911397/69925000000000000000000000000000 : ℝ)*base80 + (1046424797091/559400000000000000000000000 : ℝ)*base82 + (110409/7812500000000000000 : ℝ)*base89 + (110409/7812500000000000000 : ℝ)*base91 + (110409/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1041_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_s8_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216137093/10000000000 : ℝ)*x 0 + (539479407/1000000000 : ℝ)*x 1 + (5263981199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216137093/10000000000 : ℝ)^4117 ≤ (13456843235311/100000000000000 : ℝ)^3093 := by
    have hnat : (2216137093 : ℕ)^4117*100000000000000^3093 ≤ 13456843235311^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216137093 10000000000 13456843235311 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539479407/1000000000 : ℝ)^4117 ≤ (21989216437909/50000000000000 : ℝ)^3093 := by
    have hnat : (539479407 : ℕ)^4117*50000000000000^3093 ≤ 21989216437909^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539479407 1000000000 21989216437909 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263981199/10000000000 : ℝ)^4117 ≤ (10641180968379/25000000000000 : ℝ)^3093 := by
    have hnat : (5263981199 : ℕ)^4117*25000000000000^3093 ≤ 10641180968379^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263981199 10000000000 10641180968379 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216137093/10000000000 : ℝ), (539479407/1000000000 : ℝ), (5263981199/10000000000 : ℝ)] ![(13456843235311/100000000000000 : ℝ), (21989216437909/50000000000000 : ℝ), (10641180968379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216137093/10000000000 : ℝ)|^4117 ≤ (13456843235311/100000000000000 : ℝ)^3093
        have hw : |(-2216137093/10000000000 : ℝ)|=(2216137093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539479407/1000000000 : ℝ)|^4117 ≤ (21989216437909/50000000000000 : ℝ)^3093
        have hw : |(539479407/1000000000 : ℝ)|=(539479407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263981199/10000000000 : ℝ)|^4117 ≤ (10641180968379/25000000000000 : ℝ)^3093
        have hw : |(5263981199/10000000000 : ℝ)|=(5263981199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672515927/5000000000 : ℝ)*x 0 + (-2282514281/10000000000 : ℝ)*x 1 + (131599531/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672515927/5000000000 : ℝ)^4117 ≤ (8687858829879/20000000000000 : ℝ)^3093 := by
    have hnat : (2672515927 : ℕ)^4117*20000000000000^3093 ≤ 8687858829879^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672515927 5000000000 8687858829879 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282514281/10000000000 : ℝ)^4117 ≤ (13995981521161/100000000000000 : ℝ)^3093 := by
    have hnat : (2282514281 : ℕ)^4117*100000000000000^3093 ≤ 13995981521161^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282514281 10000000000 13995981521161 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131599531/250000000 : ℝ)^4117 ≤ (21282362157401/50000000000000 : ℝ)^3093 := by
    have hnat : (131599531 : ℕ)^4117*50000000000000^3093 ≤ 21282362157401^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131599531 250000000 21282362157401 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672515927/5000000000 : ℝ), (-2282514281/10000000000 : ℝ), (131599531/250000000 : ℝ)] ![(8687858829879/20000000000000 : ℝ), (13995981521161/100000000000000 : ℝ), (21282362157401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672515927/5000000000 : ℝ)|^4117 ≤ (8687858829879/20000000000000 : ℝ)^3093
        have hw : |(2672515927/5000000000 : ℝ)|=(2672515927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282514281/10000000000 : ℝ)|^4117 ≤ (13995981521161/100000000000000 : ℝ)^3093
        have hw : |(-2282514281/10000000000 : ℝ)|=(2282514281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131599531/250000000 : ℝ)|^4117 ≤ (21282362157401/50000000000000 : ℝ)^3093
        have hw : |(131599531/250000000 : ℝ)|=(131599531/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345031853/10000000000 : ℝ)*x 0 + (2631990629/5000000000 : ℝ)*x 1 + (-1141257129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345031853/10000000000 : ℝ)^4117 ≤ (43439294138577/100000000000000 : ℝ)^3093 := by
    have hnat : (5345031853 : ℕ)^4117*100000000000000^3093 ≤ 43439294138577^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345031853 10000000000 43439294138577 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631990629/5000000000 : ℝ)^4117 ≤ (21282362254269/50000000000000 : ℝ)^3093 := by
    have hnat : (2631990629 : ℕ)^4117*50000000000000^3093 ≤ 21282362254269^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631990629 5000000000 21282362254269 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141257129/5000000000 : ℝ)^4117 ≤ (6997990666719/50000000000000 : ℝ)^3093 := by
    have hnat : (1141257129 : ℕ)^4117*50000000000000^3093 ≤ 6997990666719^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141257129 5000000000 6997990666719 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345031853/10000000000 : ℝ), (2631990629/5000000000 : ℝ), (-1141257129/5000000000 : ℝ)] ![(43439294138577/100000000000000 : ℝ), (21282362254269/50000000000000 : ℝ), (6997990666719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345031853/10000000000 : ℝ)|^4117 ≤ (43439294138577/100000000000000 : ℝ)^3093
        have hw : |(5345031853/10000000000 : ℝ)|=(5345031853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631990629/5000000000 : ℝ)|^4117 ≤ (21282362254269/50000000000000 : ℝ)^3093
        have hw : |(2631990629/5000000000 : ℝ)|=(2631990629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141257129/5000000000 : ℝ)|^4117 ≤ (6997990666719/50000000000000 : ℝ)^3093
        have hw : |(-1141257129/5000000000 : ℝ)|=(1141257129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379099767/10000000000 : ℝ)*x 0 + (531680179/1250000000 : ℝ)*x 1 + (1127136147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379099767/10000000000 : ℝ)^4117 ≤ (8329099885951/25000000000000 : ℝ)^3093 := by
    have hnat : (4379099767 : ℕ)^4117*25000000000000^3093 ≤ 8329099885951^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379099767 10000000000 8329099885951 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531680179/1250000000 : ℝ)^4117 ≤ (16024980355563/50000000000000 : ℝ)^3093 := by
    have hnat : (531680179 : ℕ)^4117*50000000000000^3093 ≤ 16024980355563^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531680179 1250000000 16024980355563 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127136147/2500000000 : ℝ)^4117 ≤ (17316819864509/50000000000000 : ℝ)^3093 := by
    have hnat : (1127136147 : ℕ)^4117*50000000000000^3093 ≤ 17316819864509^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127136147 2500000000 17316819864509 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379099767/10000000000 : ℝ), (531680179/1250000000 : ℝ), (1127136147/2500000000 : ℝ)] ![(8329099885951/25000000000000 : ℝ), (16024980355563/50000000000000 : ℝ), (17316819864509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379099767/10000000000 : ℝ)|^4117 ≤ (8329099885951/25000000000000 : ℝ)^3093
        have hw : |(4379099767/10000000000 : ℝ)|=(4379099767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531680179/1250000000 : ℝ)|^4117 ≤ (16024980355563/50000000000000 : ℝ)^3093
        have hw : |(531680179/1250000000 : ℝ)|=(531680179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127136147/2500000000 : ℝ)|^4117 ≤ (17316819864509/50000000000000 : ℝ)^3093
        have hw : |(1127136147/2500000000 : ℝ)|=(1127136147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11080711/50000000 : ℝ)*x 0 + (2632154311/5000000000 : ℝ)*x 1 + (5394465487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11080711/50000000 : ℝ)^4117 ≤ (6728442256413/50000000000000 : ℝ)^3093 := by
    have hnat : (11080711 : ℕ)^4117*50000000000000^3093 ≤ 6728442256413^3093*50000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11080711 50000000 6728442256413 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632154311/5000000000 : ℝ)^4117 ≤ (21284123994343/50000000000000 : ℝ)^3093 := by
    have hnat : (2632154311 : ℕ)^4117*50000000000000^3093 ≤ 21284123994343^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632154311 5000000000 21284123994343 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394465487/10000000000 : ℝ)^4117 ≤ (8794973497993/20000000000000 : ℝ)^3093 := by
    have hnat : (5394465487 : ℕ)^4117*20000000000000^3093 ≤ 8794973497993^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394465487 10000000000 8794973497993 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11080711/50000000 : ℝ), (2632154311/5000000000 : ℝ), (5394465487/10000000000 : ℝ)] ![(6728442256413/50000000000000 : ℝ), (21284123994343/50000000000000 : ℝ), (8794973497993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11080711/50000000 : ℝ)|^4117 ≤ (6728442256413/50000000000000 : ℝ)^3093
        have hw : |(-11080711/50000000 : ℝ)|=(11080711/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632154311/5000000000 : ℝ)|^4117 ≤ (21284123994343/50000000000000 : ℝ)^3093
        have hw : |(2632154311/5000000000 : ℝ)|=(2632154311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394465487/10000000000 : ℝ)|^4117 ≤ (8794973497993/20000000000000 : ℝ)^3093
        have hw : |(5394465487/10000000000 : ℝ)|=(5394465487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328037211/2500000000 : ℝ)*x 0 + (-2152030047/10000000000 : ℝ)*x 1 + (2697232727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328037211/2500000000 : ℝ)^4117 ≤ (43083939615421/100000000000000 : ℝ)^3093 := by
    have hnat : (1328037211 : ℕ)^4117*100000000000000^3093 ≤ 43083939615421^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328037211 2500000000 43083939615421 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152030047/10000000000 : ℝ)^4117 ≤ (6470596615239/50000000000000 : ℝ)^3093 := by
    have hnat : (2152030047 : ℕ)^4117*50000000000000^3093 ≤ 6470596615239^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152030047 10000000000 6470596615239 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697232727/5000000000 : ℝ)^4117 ≤ (43974867131893/100000000000000 : ℝ)^3093 := by
    have hnat : (2697232727 : ℕ)^4117*100000000000000^3093 ≤ 43974867131893^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697232727 5000000000 43974867131893 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328037211/2500000000 : ℝ), (-2152030047/10000000000 : ℝ), (2697232727/5000000000 : ℝ)] ![(43083939615421/100000000000000 : ℝ), (6470596615239/50000000000000 : ℝ), (43974867131893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328037211/2500000000 : ℝ)|^4117 ≤ (43083939615421/100000000000000 : ℝ)^3093
        have hw : |(1328037211/2500000000 : ℝ)|=(1328037211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152030047/10000000000 : ℝ)|^4117 ≤ (6470596615239/50000000000000 : ℝ)^3093
        have hw : |(-2152030047/10000000000 : ℝ)|=(2152030047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697232727/5000000000 : ℝ)|^4117 ≤ (43974867131893/100000000000000 : ℝ)^3093
        have hw : |(2697232727/5000000000 : ℝ)|=(2697232727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062429769/2000000000 : ℝ)*x 0 + (674308181/1250000000 : ℝ)*x 1 + (-1076015027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062429769/2000000000 : ℝ)^4117 ≤ (5385492453277/12500000000000 : ℝ)^3093 := by
    have hnat : (1062429769 : ℕ)^4117*12500000000000^3093 ≤ 5385492453277^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062429769 2000000000 5385492453277 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674308181/1250000000 : ℝ)^4117 ≤ (43974867066789/100000000000000 : ℝ)^3093 := by
    have hnat : (674308181 : ℕ)^4117*100000000000000^3093 ≤ 43974867066789^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674308181 1250000000 43974867066789 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076015027/5000000000 : ℝ)^4117 ≤ (12941193286509/100000000000000 : ℝ)^3093 := by
    have hnat : (1076015027 : ℕ)^4117*100000000000000^3093 ≤ 12941193286509^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076015027 5000000000 12941193286509 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062429769/2000000000 : ℝ), (674308181/1250000000 : ℝ), (-1076015027/5000000000 : ℝ)] ![(5385492453277/12500000000000 : ℝ), (43974867066789/100000000000000 : ℝ), (12941193286509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062429769/2000000000 : ℝ)|^4117 ≤ (5385492453277/12500000000000 : ℝ)^3093
        have hw : |(1062429769/2000000000 : ℝ)|=(1062429769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674308181/1250000000 : ℝ)|^4117 ≤ (43974867066789/100000000000000 : ℝ)^3093
        have hw : |(674308181/1250000000 : ℝ)|=(674308181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076015027/5000000000 : ℝ)|^4117 ≤ (12941193286509/100000000000000 : ℝ)^3093
        have hw : |(-1076015027/5000000000 : ℝ)|=(1076015027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s8_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379109729/10000000000 : ℝ)*x 0 + (2253953081/5000000000 : ℝ)*x 1 + (4254082199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379109729/10000000000 : ℝ)^4117 ≤ (16658250213737/50000000000000 : ℝ)^3093 := by
    have hnat : (4379109729 : ℕ)^4117*50000000000000^3093 ≤ 16658250213737^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379109729 10000000000 16658250213737 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253953081/5000000000 : ℝ)^4117 ≤ (6925422397053/20000000000000 : ℝ)^3093 := by
    have hnat : (2253953081 : ℕ)^4117*20000000000000^3093 ≤ 6925422397053^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253953081 5000000000 6925422397053 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254082199/10000000000 : ℝ)^4117 ≤ (32056387572881/100000000000000 : ℝ)^3093 := by
    have hnat : (4254082199 : ℕ)^4117*100000000000000^3093 ≤ 32056387572881^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254082199 10000000000 32056387572881 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379109729/10000000000 : ℝ), (2253953081/5000000000 : ℝ), (4254082199/10000000000 : ℝ)] ![(16658250213737/50000000000000 : ℝ), (6925422397053/20000000000000 : ℝ), (32056387572881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379109729/10000000000 : ℝ)|^4117 ≤ (16658250213737/50000000000000 : ℝ)^3093
        have hw : |(4379109729/10000000000 : ℝ)|=(4379109729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253953081/5000000000 : ℝ)|^4117 ≤ (6925422397053/20000000000000 : ℝ)^3093
        have hw : |(2253953081/5000000000 : ℝ)|=(2253953081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254082199/10000000000 : ℝ)|^4117 ≤ (32056387572881/100000000000000 : ℝ)^3093
        have hw : |(4254082199/10000000000 : ℝ)|=(4254082199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (8233/2048 : ℝ) ≤ (7568134872294159/50000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^8233 ≤ (7568134872294159/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5607 : ℕ)^8233*50000000000000000000^2048 ≤ 7568134872294159^2048*50000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 7568134872294159 50000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (7568134872294159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (8233/2048 : ℝ) ≤ (7365471012959791/20000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^8233 ≤ (7365471012959791/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1399 : ℕ)^8233*20000000000000000000^2048 ≤ 7365471012959791^2048*10000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 7365471012959791 20000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (7365471012959791/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007568134872294159/25000000000000000000 : ℝ) ≤ (5000376479486697/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (25007568134872294159/25000000000000000000 : ℝ)^2048 ≤ (5000376479486697/5000000000000000 : ℝ)^8233 := by
      have hnat : (25007568134872294159 : ℕ)^2048*5000000000000000^8233 ≤ 5000376479486697^8233*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007568134872294159 25000000000000000000 5000376479486697 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000376479486697/5000000000000000 : ℝ)) (X := (25007568134872294159/25000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051963624809387273/100000000000000000000 : ℝ) ≤ (10001292368976163/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (100051963624809387273/100000000000000000000 : ℝ)^2048 ≤ (10001292368976163/10000000000000000 : ℝ)^8233 := by
      have hnat : (100051963624809387273 : ℕ)^2048*10000000000000000^8233 ≤ 10001292368976163^8233*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051963624809387273 100000000000000000000 10001292368976163 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001292368976163/10000000000000000 : ℝ)) (X := (100051963624809387273/100000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007365471012959791/10000000000000000000 : ℝ) ≤ (2500457944744733/2500000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (10007365471012959791/10000000000000000000 : ℝ)^2048 ≤ (2500457944744733/2500000000000000 : ℝ)^8233 := by
      have hnat : (10007365471012959791 : ℕ)^2048*2500000000000000^8233 ≤ 2500457944744733^8233*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007365471012959791 10000000000000000000 2500457944744733 2500000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500457944744733/2500000000000000 : ℝ)) (X := (10007365471012959791/10000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7568134872294159/50000000000000000000 : ℝ) ≤ ((6937498081642009653/6940000000000000000 : ℝ)+2*(539410002769/277600000000000 : ℝ)*(5607/50000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (6937498081642009653/6940000000000000000 : ℝ)+2*(539410002769/277600000000000 : ℝ)*(5607/50000 : ℝ)=(5000376479486697/5000000000000000 : ℝ) by norm_num, show 1+2*(7568134872294159/50000000000000000000 : ℝ)=(25007568134872294159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7365471012959791/20000000000000000000 : ℝ)+(7568134872294159/50000000000000000000 : ℝ) ≤ ((6937498081642009653/6940000000000000000 : ℝ)+(539410002769/277600000000000 : ℝ)*((1399/10000 : ℝ)+(5607/50000 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (6937498081642009653/6940000000000000000 : ℝ)+(539410002769/277600000000000 : ℝ)*((1399/10000 : ℝ)+(5607/50000 : ℝ))=(10001292368976163/10000000000000000 : ℝ) by norm_num, show 1+(7365471012959791/20000000000000000000 : ℝ)+(7568134872294159/50000000000000000000 : ℝ)=(100051963624809387273/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7365471012959791/20000000000000000000 : ℝ) ≤ ((6937498081642009653/6940000000000000000 : ℝ)+2*(539410002769/277600000000000 : ℝ)*(1399/10000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (6937498081642009653/6940000000000000000 : ℝ)+2*(539410002769/277600000000000 : ℝ)*(1399/10000 : ℝ)=(2500457944744733/2500000000000000 : ℝ) by norm_num, show 1+2*(7365471012959791/20000000000000000000 : ℝ)=(10007365471012959791/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6937498081642009653/6940000000000000000 : ℝ)*(X 1 0+X 2 0)+(539410002769/277600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6937498081642009653/6940000000000000000 : ℝ)) (alpha := (539410002769/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6937498081642009653/6940000000000000000 : ℝ)*(X 0 1+X 2 1)+(539410002769/277600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6937498081642009653/6940000000000000000 : ℝ)) (alpha := (539410002769/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6937498081642009653/6940000000000000000 : ℝ)*(X 0 2+X 1 2)+(539410002769/277600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6937498081642009653/6940000000000000000 : ℝ)) (alpha := (539410002769/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2216137093/10000000000 : ℝ)*X 0 0+(539479407/1000000000 : ℝ)*X 0 1+(5263981199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672515927/5000000000 : ℝ)*X 1 0+(-2282514281/10000000000 : ℝ)*X 1 1+(131599531/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345031853/10000000000 : ℝ)*X 2 0+(2631990629/5000000000 : ℝ)*X 2 1+(-1141257129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379099767/10000000000 : ℝ)*X 0 0+(531680179/1250000000 : ℝ)*X 0 1+(1127136147/2500000000 : ℝ)*X 0 2+(4379099767/10000000000 : ℝ)*X 1 0+(531680179/1250000000 : ℝ)*X 1 1+(1127136147/2500000000 : ℝ)*X 1 2+(4379099767/10000000000 : ℝ)*X 2 0+(531680179/1250000000 : ℝ)*X 2 1+(1127136147/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-11080711/50000000 : ℝ)*X 0 0+(2632154311/5000000000 : ℝ)*X 0 1+(5394465487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328037211/2500000000 : ℝ)*X 1 0+(-2152030047/10000000000 : ℝ)*X 1 1+(2697232727/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062429769/2000000000 : ℝ)*X 2 0+(674308181/1250000000 : ℝ)*X 2 1+(-1076015027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379109729/10000000000 : ℝ)*X 0 0+(2253953081/5000000000 : ℝ)*X 0 1+(4254082199/10000000000 : ℝ)*X 0 2+(4379109729/10000000000 : ℝ)*X 1 0+(2253953081/5000000000 : ℝ)*X 1 1+(4254082199/10000000000 : ℝ)*X 1 2+(4379109729/10000000000 : ℝ)*X 2 0+(2253953081/5000000000 : ℝ)*X 2 1+(4254082199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3555704344569424458598907463/347000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1011521361/50000000000000 : ℝ)*(base19) + (241275859/12500000000000 : ℝ)*(base23) + (9771319/20000000000000 : ℝ)*(lower2) + (221627523/100000000000000 : ℝ)*(upper3) + (188683199/100000000000000 : ℝ)*(upper5) + (5782333653071581/100000000000000 : ℝ)*(major0) + (5782333653071581/100000000000000 : ℝ)*(major1) + (5782333653071581/100000000000000 : ℝ)*(major2) + (7644566461886383/100000000000000 : ℝ)*(sp0) + (3822311641825119/50000000000000 : ℝ)*(sp1) + (955577922060761/12500000000000 : ℝ)*(sp2) + (3920011610461593/100000000000000 : ℝ)*(sp3) + (29422403289/50000000000000 : ℝ)*(sp4) + (15023711189/50000000000000 : ℝ)*(sp7) + (980010414470993/25000000000000 : ℝ)*(f.failure) + (47778908166831/625000000000 : ℝ)*(f.sum) + (21991841047331/13880000000000000000000000000 : ℝ)*base66 + (12386991855124696393/694000000000000000000000000000000 : ℝ)*base67 + (6416464140650696393/694000000000000000000000000000000 : ℝ)*base69 + (5956480221666696393/694000000000000000000000000000000 : ℝ)*base71 + (38511780404131/13880000000000000000000000000 : ℝ)*base74 + (8390305339252696393/694000000000000000000000000000000 : ℝ)*base75 + (4522204432138696393/694000000000000000000000000000000 : ℝ)*base77 + (7792799036792696393/694000000000000000000000000000000 : ℝ)*base79 + (54239242204029/13880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (454303/39062500000000000000 : ℝ)*base89 + (454303/39062500000000000000 : ℝ)*base91 + (454303/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1437113297123320713505846803/347000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150542597/20000000000000 : ℝ)*(base19) + (76219161/10000000000000 : ℝ)*(base23) + (64430971/100000000000000 : ℝ)*(upper3) + (4660599/100000000000000 : ℝ)*(lower4) + (12658167/20000000000000 : ℝ)*(upper5) + (5811387597874483/100000000000000 : ℝ)*(major0) + (5811387597874483/100000000000000 : ℝ)*(major1) + (5811387597874483/100000000000000 : ℝ)*(major2) + (2460830009/12500000000000 : ℝ)*(sp1) + (19566908731/100000000000000 : ℝ)*(sp2) + (7683036737395679/100000000000000 : ℝ)*(sp4) + (3841508149021311/50000000000000 : ℝ)*(sp5) + (7683016408295339/100000000000000 : ℝ)*(sp6) + (123116822509439/3125000000000 : ℝ)*(sp7) + (123116822509439/3125000000000 : ℝ)*(f.failure) + (7683036737395679/100000000000000 : ℝ)*(f.sum) + (19554347701533/13880000000000000000000000000 : ℝ)*base66 + (7496620739338059399/694000000000000000000000000000000 : ℝ)*base67 + (10995293877695940601/694000000000000000000000000000000 : ℝ)*base70 + (2380700265542059399/694000000000000000000000000000000 : ℝ)*base71 + (1029454700627/13880000000000000000000000000 : ℝ)*base73 + (4820689219774059399/694000000000000000000000000000000 : ℝ)*base75 + (3467740543394059399/694000000000000000000000000000000 : ℝ)*base77 + (14024503956269940601/694000000000000000000000000000000 : ℝ)*base80 + (26298187990813/13880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (166323/39062500000000000000 : ℝ)*base90 + (166323/39062500000000000000 : ℝ)*base92 + (166323/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1041_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1041_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1041_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1041_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1041_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
